-- Prove2me | Theorems.Thm_BitcoinScriptV2_evalOk_of_static
-- name    : BitcoinScriptV2.evalOk_of_static
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:21:30.126716+00:00
-- url     : https://prove2.me/theorems/4eec812c-7b09-4c15-900d-8ea426370a65
-- title:
--   Static sufficient condition for EvalOk
-- statement:
--   If every parse of the script satisfies `NoCodeSep ∧ NoMultisig`, then `EvalOk c v stack script`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.evalOk_of_static (c : BitcoinVerify.Ctx) (v : BitcoinSig.SigVersion)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes)
    (h : ∀ s, BitcoinSig.parseScript script = some s → BitcoinScriptV2.NoCodeSep s ∧ BitcoinScriptV2.NoMultisig s) :
    BitcoinScriptV2.EvalOk c v stack script := by sorry
