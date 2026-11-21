-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_lk_negative_mark_cutoff_identity
-- name    : AvramDividend.Classical.original_lk_negative_mark_cutoff_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:15:04.416412+00:00
-- url     : https://prove2.me/theorems/5b579263-d78e-4302-a64a-3621ecf687f3
-- title:
--   Exact original Lévy-Khintchine compensator cutoff split at negative mark −1
-- statement:
--   For each original negative jump mark y<0 and positive Laplace parameter θ, its exact LK compensated jump contribution divided by θ equals the common nonnegative exponential primitive at magnitude −y plus y when y≤−1 and zero otherwise. The original indicator Ioo(-1,1) is respected at y=−1, so this identity carries all boundary conventions into the real-integral exponent formula.
-- source:
--   Proved/under-verification compensated_jump_exponential_primitive and exact original laplaceExponent truncation in Prove2Me; stepping stone to original_purejump_lk_mark_decomposition (7a6e6fc3).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_compensated_jump_exponential_primitive
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.original_lk_negative_mark_cutoff_identity
    (θ y : ℝ) (hθ : 0 < θ) (hy : y < 0) :
    (Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) / θ =
    (if y ≤ -1 then y else 0) +
      (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) := by sorry
