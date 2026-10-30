-- Prove2me | Theorems.Thm_BitcoinScriptV2_stepV2_agree
-- name    : BitcoinScriptV2.stepV2_agree
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:20:34.087244+00:00
-- url     : https://prove2.me/theorems/2e47d6c0-1503-40f6-9cb5-27e9513e4a03
-- title:
--   Outside the two limits a V2 step is the published step
-- statement:
--   Under `StepOk v s i` and `scriptCode = sc`: `stepV2 f v o s (i, r) = (step f (withCodeSig o v sc) s.st i).map (⟨·, sc⟩)`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.stepV2_agree (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (s : BitcoinScriptV2.StateV2) (sc : BitcoinScript.Bytes) (hsc : s.scriptCode = sc)
    (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes) (hok : BitcoinScriptV2.StepOk v s i) :
    BitcoinScriptV2.stepV2 f v o s (i, r) =
      (BitcoinScript.step f (BitcoinScriptV2.withCodeSig o v sc) s.st i).map fun st => ⟨st, sc⟩ := by sorry
