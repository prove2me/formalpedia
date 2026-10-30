-- Prove2me | Theorems.Thm_BitcoinScriptV2_eval_agree
-- name    : BitcoinScriptV2.eval_agree
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:20:45.627879+00:00
-- url     : https://prove2.me/theorems/12f71cae-47d5-4321-9f78-35f27d972e80
-- title:
--   Outside the two limits the V2 evaluator is the published evaluator
-- statement:
--   Under `RunOk` along the run: `evalScriptV2 f v o stack script = evalScript f (withCodeSig o v script) stack (l.map Prod.fst)` for the annotated parse `l`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.eval_agree (f : BitcoinScript.Flags) (v : BitcoinSig.SigVersion) (o : BitcoinScriptV2.OracleV2)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (hl : BitcoinScriptV2.annotate script = some l)
    (hok : BitcoinScriptV2.RunOk f v o ⟨BitcoinScript.State.initial stack, script⟩ l) :
    BitcoinScriptV2.evalScriptV2 f v o stack script =
      BitcoinScript.evalScript f (BitcoinScriptV2.withCodeSig o v script) stack (l.map Prod.fst) := by sorry
