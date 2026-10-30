-- Prove2me | Theorems.Thm_BitcoinScriptV2_fadAll_base
-- name    : BitcoinScriptV2.fadAll_base
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:19:46.461528+00:00
-- url     : https://prove2.me/theorems/374c8843-87ed-4033-999e-3820256adf47
-- title:
--   In SigVersion::BASE, deleting all signatures is a fold of FindAndDelete
-- statement:
--   `fadAll .base sc sigs = sigs.foldl (fun sc sig => (findAndDelete sc (pushBytes sig)).1) sc`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.fadAll_base (sc : BitcoinScript.Bytes) (sigs : List BitcoinScript.Bytes) :
    BitcoinScriptV2.fadAll .base sc sigs =
      sigs.foldl (fun sc sig => (BitcoinSig.findAndDelete sc (BitcoinSig.pushBytes sig)).1) sc := by sorry
