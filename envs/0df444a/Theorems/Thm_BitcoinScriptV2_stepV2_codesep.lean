-- Prove2me | Theorems.Thm_BitcoinScriptV2_stepV2_codesep
-- name    : BitcoinScriptV2.stepV2_codesep
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:18:59.895007+00:00
-- url     : https://prove2.me/theorems/4cd75e5e-244f-4cc9-87e5-2c4eaa0125f0
-- title:
--   An executed OP_CODESEPARATOR resets the script code to its suffix
-- statement:
--   If `stepV2` executes `(.op OP_CODESEPARATOR, r)` from an executing state and succeeds, the new `scriptCode` is `r`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.stepV2_codesep (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s s' : BitcoinScriptV2.StateV2) (r : BitcoinScript.Bytes) (hexec : BitcoinScript.allTrue s.st.vfExec = true)
    (h : BitcoinScriptV2.stepV2 f v o s (.op BitcoinScript.OP_CODESEPARATOR, r) = some s') :
    s'.scriptCode = r := by sorry
