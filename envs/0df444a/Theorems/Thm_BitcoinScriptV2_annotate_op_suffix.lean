-- Prove2me | Theorems.Thm_BitcoinScriptV2_annotate_op_suffix
-- name    : BitcoinScriptV2.annotate_op_suffix
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T23:18:47.841068+00:00
-- url     : https://prove2.me/theorems/c2266565-a15a-45a3-86ab-2aecd23ab9df
-- title:
--   An opcode's annotation is the bytes after its position
-- statement:
--   If `annotate s = some l` and `(.op c, r) ∈ l` then there is a position $p$ with `s[p]? = some c` and `r = s.drop (p+1)`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (pbegincodehash, OP_CODESEPARATOR at interpreter.cpp:1058-1066, OP_CHECKSIG's scriptCode and FindAndDelete at :339-343 / the CHECKSIG case, OP_CHECKMULTISIG's deletion of every signature at :1152-1159), SignatureHash (SigVersion::BASE), VerifyScript (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); Core's script_tests.json, tx_valid.json, tx_invalid.json at the same revision

import Definitions.Def_BitcoinScriptV2
import Definitions.Def_BitcoinScript
open BitcoinScriptV2 BitcoinScript BitcoinSig BitcoinVerify

theorem BitcoinScriptV2.annotate_op_suffix (s : BitcoinScript.Bytes) (l : List (BitcoinScript.Instr × BitcoinScript.Bytes))
    (h : BitcoinScriptV2.annotate s = some l) (c : BitcoinScript.Byte) (r : BitcoinScript.Bytes) (hm : (.op c, r) ∈ l) :
    ∃ p, s[p]? = some c ∧ r = s.drop (p + 1) := by sorry
