-- Prove2me | Theorems.Thm_BitDFT_double_high_multiplier_call
-- name    : BitDFT.double_high_multiplier_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T01:49:14.674177+00:00
-- url     : https://prove2.me/theorems/04bdf1e1-2c5a-49ad-a8a3-41972dd27bc2
-- title:
--   One q-bit multiplier call handles two boundary-width magnitudes
-- statement:
--   Suppose a multitape machine multiplies q-bit words within T steps. For magnitudes a,b≤2^q, a clean invocation on their q-bit residues modulo 2^q runs in at most 36T steps and returns the exact residue product. The full product ab is then recovered from that residue product and the q-th bits: if a=2^q or b=2^q, only a shift is needed; otherwise the residue product is already ab. Hence the boundary cases require no call at width q+1.
-- source:
--   Runtime-bearing width reduction for each signed coordinate product in the fixed-point multiplication machine.

import Theorems.Thm_BitDFT_clean_multiplier_call
import Theorems.Thm_BitDFT_scalar_low_product_selection
import Mathlib.Tactic
open IntMul

theorem BitDFT.double_high_multiplier_call (M : MultitapeTM) (q : ℕ) (a b : ℕ) (T : ℝ)
    (hq : 1 ≤ q) (ha : a ≤ 2^q) (hb : b ≤ 2^q)
    (hM : MultipliesAt M q T) :
    ∃ t : ℕ, (t : ℝ) ≤ 36 * T ∧
      (IntMul.TrackedNativeCall.machine M).HaltsWithOutput
        (bin q (a % 2^q)) (bin q (b % 2^q)) t
        (bin (2*q) ((a % 2^q) * (b % 2^q))) ∧
      a*b = if a.testBit q then 2^q*b
        else if b.testBit q then (a % 2^q)*2^q
        else (a % 2^q)*(b % 2^q) := by sorry
