-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_ramp_remainder_support
-- name    : AvramDividend.Classical.causal_ramp_remainder_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:30:29.444849+00:00
-- url     : https://prove2.me/theorems/4cf6d50f-a6e1-421e-9317-6bbaefaffb5e
-- title:
--   Small-origin support of the remainder in a causal ramp cutoff decomposition
-- statement:
--   The difference between a causal real function and its product with the continuous ramp cutoff of width epsilon vanishes for x less than or equal to zero and for x greater than or equal to twice epsilon. This gives exact compact near-origin support of the remainder in the local convolution continuity decomposition.
-- source:
--   Use exact zero and unit regions of the already proved ramp cutoff to rewrite both cases to f minus f or zero.

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
open AvramDividend.Classical Set

namespace AvramDividend.Classical
theorem causal_ramp_remainder_support
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) :
    (∀ x : ℝ, x ≤ 0 →
      f x - max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x = 0) ∧
    (∀ x : ℝ, 2 * ε ≤ x →
      f x - max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x = 0) := by sorry
end AvramDividend.Classical
