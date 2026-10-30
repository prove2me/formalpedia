-- Prove2me | Theorems.Thm_BitcoinScriptV2_stepV2_keeps
-- name    : BitcoinScriptV2.stepV2_keeps
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:19:12.333229+00:00
-- url     : https://prove2.me/theorems/9fd2f000-6bba-47bc-b6ee-c68fb337c2e7
-- title:
--   Every other step keeps the script code
-- statement:
--   If the instruction is not an executed code separator, `stepV2` leaves `scriptCode` unchanged.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.stepV2_keeps (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s s' : BitcoinScriptV2.StateV2) (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes)
    (hno : i ≠ .op BitcoinScript.OP_CODESEPARATOR ∨ BitcoinScript.allTrue s.st.vfExec = false)
    (h : BitcoinScriptV2.stepV2 f v o s (i, r) = some s') :
    s'.scriptCode = s.scriptCode := by sorry
