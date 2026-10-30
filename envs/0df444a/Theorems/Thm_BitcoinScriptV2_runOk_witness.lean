-- Prove2me | Theorems.Thm_BitcoinScriptV2_runOk_witness
-- name    : BitcoinScriptV2.runOk_witness
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:21:18.336031+00:00
-- url     : https://prove2.me/theorems/e1ee03a6-a2bf-4840-b362-be55082bf3b8
-- title:
--   In witness v0 only OP_CODESEPARATOR matters
-- statement:
--   `NoCodeSep` alone implies `RunOk` for `SigVersion::WITNESS_V0` (no `FindAndDelete` there).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.runOk_witness (f : BitcoinScript.Flags) (o : BitcoinScriptV2.OracleV2)
    (l : List (BitcoinScript.Instr × BitcoinScript.Bytes)) (s : BitcoinScriptV2.StateV2)
    (h1 : BitcoinScriptV2.NoCodeSep (l.map Prod.fst)) :
    BitcoinScriptV2.RunOk f .witnessV0 o s l := by sorry
