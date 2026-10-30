-- Prove2me | Theorems.Thm_BitcoinScriptV2_annotate_suffix
-- name    : BitcoinScriptV2.annotate_suffix
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:18:34.117019+00:00
-- url     : https://prove2.me/theorems/aa11677a-9e61-4fd8-a298-a14eedf3bd79
-- title:
--   Every annotation is a suffix of the script
-- statement:
--   If `annotate s = some l` and `(i, r) ∈ l` then `s = pre ++ r` for some `pre`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.annotate_suffix (s : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (h : BitcoinScriptV2.annotate s = some l) (i : BitcoinScript.Instr) (r : BitcoinScript.Bytes) (hm : (i, r) ∈ l) :
    ∃ pre, s = pre ++ r := by sorry
