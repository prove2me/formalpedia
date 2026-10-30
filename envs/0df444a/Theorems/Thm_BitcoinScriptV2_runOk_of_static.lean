-- Prove2me | Theorems.Thm_BitcoinScriptV2_runOk_of_static
-- name    : BitcoinScriptV2.runOk_of_static
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:21:06.595211+00:00
-- url     : https://prove2.me/theorems/a1e4100a-bff9-491b-8989-15cdea6d627d
-- title:
--   Scripts without OP_CODESEPARATOR and OP_CHECKMULTISIG are always outside the limits
-- statement:
--   `NoCodeSep` and `NoMultisig` of the parsed script imply `RunOk` from any state.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.runOk_of_static (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (l : List (BitcoinScript.Instr × BitcoinScript.Bytes)) (s : BitcoinScriptV2.StateV2)
    (h1 : BitcoinScriptV2.NoCodeSep (l.map Prod.fst)) (h2 : BitcoinScriptV2.NoMultisig (l.map Prod.fst)) :
    BitcoinScriptV2.RunOk f v o s l := by sorry
