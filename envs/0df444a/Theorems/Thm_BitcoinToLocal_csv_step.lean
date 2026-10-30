-- Prove2me | Theorems.Thm_BitcoinToLocal_csv_step
-- name    : BitcoinToLocal.csv_step
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:09:34.746087+00:00
-- url     : https://prove2.me/theorems/a5242a15-6490-45f7-8ee0-e8a5c2cc772a
-- title:
--   OP_CHECKSEQUENCEVERIFY on a serialized number passes exactly when CsvPasses holds
-- statement:
--   For a state whose stack top is `serialize delay` with $|{\rm delay}| < 2^{32}$: `execOp f o true OP_CHECKSEQUENCEVERIFY s = if CsvPasses f o delay then some s else none`.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.csv_step (f : Flags) (o : Oracle) (s : State) (delay : Int) (rest : List Bytes)
    (hs : s.stack = BitcoinScript.serialize delay :: rest) (hd : delay.natAbs < 2 ^ 32) :
    BitcoinScript.execOp f o true BitcoinScript.OP_CHECKSEQUENCEVERIFY s =
      if BitcoinToLocal.CsvPasses f o delay then some s else none := by sorry
