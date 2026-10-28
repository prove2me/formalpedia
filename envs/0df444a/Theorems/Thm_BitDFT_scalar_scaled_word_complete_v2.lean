-- Prove2me | Theorems.Thm_BitDFT_scalar_scaled_word_complete_v2
-- name    : BitDFT.scalar_scaled_word_complete_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:04:13.627086+00:00
-- url     : https://prove2.me/theorems/9e748f3f-0120-4845-8899-c97ad66e2d90
-- title:
--   A q-bit multiplication call yields the exact widened scaled word, including the boundary magnitude
-- statement:
--   For every n≥1 and requested q-bit multiplier width satisfying lg(n)+1≤q, a coordinate magnitude at most 2^q can be scaled by n with one q-bit multiplication call: feed n and the low q bits of the magnitude to the multiplier, then use its high bit to select either that product or n·2^q. The selected value is exactly n times the original magnitude, fits in q+lg(n)+1 bits, and its 2q-bit multiplier output is the correctly zero-padded encoding at that wider width. This includes the boundary magnitude 2^q.
-- source:
--   Formal composition of the accepted BitDFT.scalar_low_product_selection, BitDFT.scaled_product_word_direct, and BitDFT.bin_padding lemmas. This closes the scalar arithmetic and serialization-width boundary case; it does not by itself prove the multitape controller or the repeated vector-scaling wrapper.

import Theorems.Thm_BitDFT_bin_padding
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Theorems.Thm_BitDFT_scaled_product_word_direct
import Mathlib.Tactic
set_option autoImplicit false
open IntMul

theorem BitDFT.scalar_scaled_word_complete_v2 (q n a : ℕ) (hq : lg n + 1 ≤ q)
    (hn : n ≤ 2^(lg n)) (ha : a ≤ 2^q) :
    (if a.testBit q then n * 2^q else n * (a % 2^q)) = n * a ∧
    (if a.testBit q then n * 2^q else n * (a % 2^q)) < 2^(q + lg n + 1) ∧
    bin (2*q) (if a.testBit q then n * 2^q else n * (a % 2^q)) =
      List.replicate (2*q-(q+lg n+1)) false ++
      bin (q+lg n+1) (if a.testBit q then n * 2^q else n * (a % 2^q)) := by sorry
