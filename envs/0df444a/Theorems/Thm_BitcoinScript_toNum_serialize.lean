-- Prove2me | Theorems.Thm_BitcoinScript_toNum_serialize
-- name    : BitcoinScript.toNum_serialize
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T05:43:25.494034+00:00
-- url     : https://prove2.me/theorems/7a82db18-c865-4bd6-a844-040102dc1ae2
-- title:
--   A serialized number of at most four bytes is accepted strictly and reads back
-- statement:
--   For every integer $n$ whose serialization has at most four bytes, $\mathrm{toNum}(\mathtt{true}, 4, \mathrm{serialize}(n)) = \mathrm{some}\ n$: the strict (`fRequireMinimal`) four-byte constructor accepts the serializer's output and returns the original value.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CastToBool (lines 46-59), EvalScript (417-1249), EvalChecksigPreTapscript, VerifyScript (2012-2110), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CScriptNum (227-382), opcodetype, MAX_SCRIPT_ELEMENT_SIZE, MAX_OPS_PER_SCRIPT, MAX_PUBKEYS_PER_MULTISIG, MAX_STACK_SIZE, src/script/script.h; GetScriptOp, IsPushOnly, IsPayToScriptHash, src/script/script.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/script.h

import Definitions.Def_BitcoinScript

theorem BitcoinScript.toNum_serialize (n : Int) (h : (BitcoinScript.serialize n).length ≤ 4) :
    BitcoinScript.toNum true 4 (BitcoinScript.serialize n) = some n := by sorry
