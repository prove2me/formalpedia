-- Prove2me | Theorems.Thm_BitDFT_shared_alphabet_core_symbols
-- name    : BitDFT.shared_alphabet_core_symbols
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:16:01.564475+00:00
-- url     : https://prove2.me/theorems/1cbb3e34-09e7-4c64-8167-6d1224431281
-- title:
--   Binary packets have identical encodings in both shared-alphabet embeddings
-- statement:
--   For two fixed multitape machines, the shared product alphabet encodes their blank, marker, zero, one, separator, and Boolean tape symbols identically under either component embedding. Thus a binary input or output packet prepared in one component's encoding is already the same packet in the other component's encoding.
-- source:
--   Direct finite-alphabet calculation from the published product alphabet and its two injective embeddings. This is the symbol-level handoff fact needed when routing binary packets between the Fourier child and multiplier stages.

import Definitions.Def_BitDFT_SharedAlphabet
set_option autoImplicit false
open IntMul BitDFT.SharedAlphabet

theorem BitDFT.shared_alphabet_core_symbols (A M : MultitapeTM) :
    (left A M).encode A.blank = (right A M).encode M.blank ∧
    (left A M).encode A.startSym = (right A M).encode M.startSym ∧
    (left A M).encode A.zero = (right A M).encode M.zero ∧
    (left A M).encode A.one = (right A M).encode M.one ∧
    (left A M).encode A.sep = (right A M).encode M.sep ∧
    (∀ b : Bool, (left A M).encode (A.bitSym b) = (right A M).encode (M.bitSym b)) := by sorry
