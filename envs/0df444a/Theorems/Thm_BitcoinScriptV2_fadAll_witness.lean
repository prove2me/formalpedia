-- Prove2me | Theorems.Thm_BitcoinScriptV2_fadAll_witness
-- name    : BitcoinScriptV2.fadAll_witness
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:19:57.817397+00:00
-- url     : https://prove2.me/theorems/4aa4db93-4ab9-4fe8-8bfd-3ffef232c809
-- title:
--   In witness v0 nothing is deleted
-- statement:
--   `fadAll .witnessV0 sc sigs = sc`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.fadAll_witness (sc : BitcoinScript.Bytes) (sigs : List BitcoinScript.Bytes) :
    BitcoinScriptV2.fadAll .witnessV0 sc sigs = sc := by sorry
