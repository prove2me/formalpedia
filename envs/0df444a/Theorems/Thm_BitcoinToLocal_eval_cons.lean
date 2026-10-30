-- Prove2me | Theorems.Thm_BitcoinToLocal_eval_cons
-- name    : BitcoinToLocal.eval_cons
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:09:43.703009+00:00
-- url     : https://prove2.me/theorems/77987fc9-7da7-4d30-a5e5-bdcf0b7be80f
-- title:
--   The script on a stack b :: tl: it needs exactly one more element, and leaves the chosen signature check
-- statement:
--   For keys of at most 520 bytes, $|{\rm delay}| < 2^{32}$ and `tl.length + 1 ≤ 1000`: `evalScript f o (b :: tl) (toLocalScript rev delay dpk)` is `none` when `tl` is empty, and for `tl = sig :: rest` it is `(o.checkSig sig rev).map (fun ok => boolBytes ok :: rest)` when `castToBool b`, else `(o.checkSig sig dpk).map (…)` when `CsvPasses f o delay`, else `none`. The whole interpreter run, instruction by instruction, with the skipped branch's pushes and opcodes accounted for.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.eval_cons (f : Flags) (o : Oracle) (rev dpk b : Bytes) (delay : Int) (tl : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) (htl : tl.length + 1 ≤ BitcoinScript.MAX_STACK_SIZE) :
    BitcoinScript.evalScript f o (b :: tl) (BitcoinToLocal.toLocalScript rev delay dpk) =
      match tl with
      | [] => none
      | sig :: rest =>
        if BitcoinScript.castToBool b then (o.checkSig sig rev).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else if BitcoinToLocal.CsvPasses f o delay then (o.checkSig sig dpk).map (fun ok => BitcoinScript.boolBytes ok :: rest)
        else none := by sorry
