-- Prove2me | Theorems.Thm_BitcoinScriptV2_evalBytes_agree
-- name    : BitcoinScriptV2.evalBytes_agree
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:20:57.150088+00:00
-- url     : https://prove2.me/theorems/6d801f09-5b64-4268-b4a9-e9975fdd7d3e
-- title:
--   Outside the two limits the V2 byte-level evaluator is the published one
-- statement:
--   Under `EvalOk c v stack script`: `evalBytesV2 c v stack script = evalBytes c v stack script`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.evalBytes_agree (c : BitcoinVerify.Ctx) (v : BitcoinSig.SigVersion)
    (stack : List BitcoinScript.Bytes) (script : BitcoinScript.Bytes) (h : BitcoinScriptV2.EvalOk c v stack script) :
    BitcoinScriptV2.evalBytesV2 c v stack script = BitcoinVerify.evalBytes c v stack script := by sorry
