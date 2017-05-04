open System
open System.IO
open SVMAST
open ParserUtils
open SVM
open Microsoft.FSharp.Text.Lexing

let getLabels (p:Program) =
    let labels = 
        p 
        |> List.mapi (fun line I -> line,I)
        |> List.filter (fun (_,I) -> match I with Label(_,_) -> true |_->false)
        // Other Instructions are already filtered
        |> List.map (fun (line,Instruction) -> line , match Instruction with Label(name,_) -> name)

    // error check for doubles
    let rec _check l =
        match l with
        | [] -> ()
        | (_,name)::tail -> 
            if tail |> List.forall (fun (_,name2) -> name <> name2) then
                _check tail
            else
                failwithf "label %s may only exists once" name
    _check labels
    labels



type ValueType =
    | Int of int
    | Float of float
    | String of string
    | Empty

let ValueTypeToString (vt:ValueType) : string =
    match vt with
    | Int n -> n |> string
    | Float f -> f |> string
    | String s -> s
    | Empty -> "Empty"

type state = {
    PC : int
    reg1 : ValueType
    reg2 : ValueType
    reg3 : ValueType
    reg4 : ValueType
    addresses : ValueType list
}
let CreateEmptyState nAddresses =
    {
        PC = 0
        reg1 = Empty
        reg2 = Empty
        reg3 = Empty
        reg4 = Empty
        addresses = [0..nAddresses-1] |> List.map (fun _ -> Empty)
    }

let pc1 (state:state) = {state with PC = state.PC+1 }

let dumpState (state:state) =
    let concatWith c =
        fun (l:string) (r:string) ->
            sprintf "%s%c%s" l c r
    let concatWithT = concatWith '\t'
    let concatWithN = concatWith '\n'

    let Addresses =
        state.addresses |> List.mapi (fun i ad -> i/10, ad) 
        |> List.groupBy (fun (row,_) -> row)
        |> List.map (fun (_, row) -> row |> List.map (fun (_,ad) -> ValueTypeToString ad) |> List.reduce concatWithT)
        |> List.reduce concatWithN

    "MEMORY:\n"+
    Addresses+
    "\n============\n"+
    "REGISTERS:\n"+
    sprintf "%s\t%s\t%s\t%s\t\n" (ValueTypeToString state.reg1) (ValueTypeToString state.reg2) (ValueTypeToString state.reg3) (ValueTypeToString state.reg4) +
    "============\n"+
    "PROGRAM COUNTER:\n"+
    (state.PC |> string) + "\n\n"

let getRegisterValue state (regName:Register) =
    match regName with
    | Reg1 -> state.reg1
    | Reg2 -> state.reg2
    | Reg3 -> state.reg3
    | Reg4 -> state.reg4

let getRegisterValueInt state (regName:Register) =
    match getRegisterValue state regName with
    | Int n -> n
    | _ -> failwith "only ints allowd"
    

let getValueFromAdresse (state:state) (n:int) : ValueType =
    state.addresses |> List.item n

let rec getValue (state:state) (lit:Literal) =
    match lit with    
    | Literal.Integer (n, arg2Pos) -> Int n
    | Literal.Float (f, arg2Pos) -> Float f
    | Literal.String(s, arg2Pos) -> String s
    | Literal.Address(lit) ->         
        match getValue state lit with
        | Int n -> n
        | _ -> failwith "Adresse should be a Int or Addresse"
        |> getValueFromAdresse state 
    | Literal.Register(r,pos) -> getRegisterValue state r

let getIntValue (state:state) (lit:Literal) =
    match getValue state lit with
    | Int n -> n
    | _ -> failwith "Adresse should be a Int or Addresse"
    

let updateAddresses state adIndex value =
    let rec _replace n l =
        match n, l with
        | 0, _::t -> value::t
        | _, h::t -> h::(_replace (n-1) t)
        | _ -> failwith "error"
    _replace adIndex state.addresses

let updateRegister state r value =
    match r with
    | Reg1 -> {state with reg1 = value}
    | Reg2 -> {state with reg2 = value}
    | Reg3 -> {state with reg3 = value}
    | Reg4 -> {state with reg4 = value}

let move state (arg1: Literal) (arg2: Literal) pos = 
    match arg1 with
    | Address lit ->
        let adIndex = getIntValue state lit
        {state with addresses = updateAddresses state adIndex (getValue state arg2)}
    | Register (r, pos) -> updateRegister state r (getValue state arg2)
    | _ -> failwith "you can't update a constant"

/// <summary>
/// AND:
/// If both arguments are >= 0 then
/// it stores 1 into Arg1, otherwise -
/// 1. It accepts only integer num-
/// bers, otherwise it raises a run-
/// time exception.
/// </summary>
/// <param name="state"></param>
/// <param name="arg1">Register</param>
/// <param name="arg2">Register,Address, or Constant</param>
let _and state (arg1:Register) (arg2:Literal ) =
    let arg1IntValue = getRegisterValueInt state arg1
    if arg1IntValue > 0 && (getIntValue state arg2) > 0 then
        updateRegister state arg1 (Int 1)
    else
        updateRegister state arg1 (Int -1)

let _or state (arg1:Register) (arg2:Literal) =
    let arg1IntValue = getRegisterValueInt state arg1
    if arg1IntValue > 0 || (getIntValue state arg2) > 0 then
        updateRegister state arg1 (Int 1)
    else
        updateRegister state arg1 (Int -1)

let _not state (arg1:Register) =
    if getRegisterValueInt state arg1 >= 0 then
        updateRegister state arg1 (Int -1)
    else
        updateRegister state arg1 (Int 0)

let _op opInt opFloat state (arg1:Register) (arg2:Literal)  =
    let v1, v2 = getRegisterValue state arg1 , getValue state arg2
    updateRegister state arg1 <|
    match v1, v2 with
    | Int n1, Int n2 -> (Int (opInt n1 n2))
    | Float f1, Float f2 -> (Float(opFloat f1 f2))
    | _ -> failwith "the only supported types for this operation are are (float*float) and (int*int)"

let _mod = _op (%) (%)
let _add = _op (+) (+)
let _sub = _op (-) (-)
let _mul = _op (*) (*)
let _div = _op (/) (/)

let _cmp state (arg1:Register) (arg2:Literal) =
    let v1, v2 = getRegisterValue state arg1 , getValue state arg2
    updateRegister state arg1 <|
    match v1, v2 with
    | Int n1, Int n2 -> Int(if n1 < n2 then -1 else if n1 = n2 then 0 else 1)
    | Float f1, Float f2 -> Int(if f1 < f2 then -1 else if f1 = f2 then 0 else 1)
    | _ -> failwith "the only supported types for this operation are are (float*float) and (int*int)"

let _jmpIf b state labels id =
    match labels |> List.tryFind (fun (_,namelabel) -> id = namelabel) with
    | Some(line,_) -> 
        if b then
            {state with PC = line}
        else
            pc1 state
    | None -> failwithf "could not find a label with the name %s" id  
    
let _jmp = _jmpIf true
    
let _jc state labels  id (reg:Register) =
    let b = getRegisterValueInt state reg >= 0
    _jmpIf b state labels id
      
let _jeq state labels  id (reg:Register) =
    let b = getRegisterValueInt state reg = 0
    _jmpIf b state labels id

let executeStep (program:Program) (labels:(int*string) list) (state:state) : (state*state) Option =
    let instruction = 
        if state.PC >= (program |> List.length) then
            Nop (0,0)
        else
            program |> List.item state.PC
    
    match instruction with
    | Nop _ when state.PC > (program |> List.length) -> None
    | _ ->
    Some(state, 
        match instruction with
        | Nop _ -> state |> pc1 //include the last frame
        | Mov(arg1,arg2,pos) -> move state arg1 arg2 pos |> pc1
        | And (arg1,arg2, pos) -> (_and state arg1 arg2) |> pc1
        | Or(arg1,arg2,pos) -> _or state arg1 arg2 |> pc1
        | Not(reg,pos) -> _not state reg |> pc1
        | Mod(arg1,arg2, pos) -> _mod state arg1 arg2 |> pc1
        | Add(arg1,arg2,pos) -> _add state arg1 arg2 |> pc1
        | Sub(arg1,arg2,pos) -> _sub state arg1 arg2 |> pc1
        | Mul(arg1,arg2,pos) -> _mul state arg1 arg2 |> pc1
        | Div(arg1,arg2,pos) -> _div state arg1 arg2 |> pc1
        | Cmp(arg1,arg2,pos) -> _cmp state arg1 arg2 |> pc1
        | Jmp(label,pos) -> _jmp state labels label
        | Jc(label,reg,pos) -> _jc state labels label reg
        | Jeq(label,reg,pos) -> _jeq state labels label reg
        | Label _ -> state |> pc1
        | _ -> failwith "action not suported" //will never be reached at the moment
    )



let parseFile (fileName : string) =
  let inputChannel = new StreamReader(fileName)
  let lexbuf = LexBuffer<char>.FromTextReader inputChannel
  let parsedAST = Parser.start Lexer.tokenstream lexbuf
  parsedAST

[<EntryPoint>]
let main argv =
  try
    if argv.Length = 2 then
      let ast = parseFile argv.[0]
      let labels = getLabels ast
      let state = CreateEmptyState (int argv.[1])
      let executeStep = executeStep ast labels
      let steps = Seq.unfold executeStep state
      do  printfn "%A" ast
      do  steps |> Seq.iter (fun state -> (printfn "%s" (dumpState state)))
      Console.Read() |> ignore
      0
    else
      do printfn "You must specify a command line argument containing the path to the program source file and the size of the memory"
      1
  with
  | ParseError(msg,row,col) ->
      do printfn "Parse Error: %s at line %d column %d" msg row col
      1
  | :? Exception as e ->
      do printfn "%s" e.Message
      1
