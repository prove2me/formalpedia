-- Prove2me | Theorems.Thm_BitDFT_scaled_call_word
-- name    : BitDFT.scaled_call_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T22:07:35.283555+00:00
-- url     : https://prove2.me/theorems/c2e3ed9f-8be8-46cd-9d71-610e433ca527
-- title:
--   One q-bit multiplier call provides the exact output word for a scaled magnitude
-- statement:
--   Let a fixed machine multiply every pair of q-bit integers within time T. Suppose q is large enough that n fits in q bits and lg(n)+1≤q, and let a≤2^q be a signed magnitude. Then the clean call on n and the low q bits of a halts within 36T and outputs their exact 2q-bit product. The high bit of a determines whether this product is already the desired scaled magnitude or whether the exact value n·2^q is selected. In both cases, the selected value is n·a and its encoding at width q+lg(n)+1 is the corresponding zero-padded output word. This records the machine call and the boundary case in one result.
-- source:
--   Composition of the accepted clean arbitrary-multiplier call with the accepted high-bit selection, fixed-width padding, and direct output-width lemmas. This establishes the single-coordinate call/word interface; iteration over a full vector and the complete wrapper remain open.

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Theorems.Thm_BitDFT_scaled_product_word_direct
import Theorems.Thm_BitDFT_bin_padding
import Definitions.Def_BitDFT_Encoding
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
set_option autoImplicit false
open BitDFT IntMul

theorem BitDFT.scaled_call_word (M : MultitapeTM) (q n a : ℕ) (T : ℝ)
    (hq : 1 ≤ q) (hnq : n < 2^q) (hqwide : lg n + 1 ≤ q)
    (hnwide : n ≤ 2^(lg n)) (ha : a ≤ 2^q)
    (hM : MultipliesAt M q T) :
    ∃ t : ℕ, (t : ℝ) ≤ 36*T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q n) (bin q (a%2^q)) t (bin (2*q) (n*(a%2^q))) ∧
      (if a.testBit q then n*2^q else n*(a%2^q)) = n*a ∧
      bin (2*q) (if a.testBit q then n*2^q else n*(a%2^q)) =
        List.replicate (2*q-(q+lg n+1)) false ++
          bin (q+lg n+1) (if a.testBit q then n*2^q else n*(a%2^q)) := by sorry
