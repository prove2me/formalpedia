-- Prove2me | Theorems.Thm_AvramDividend_Classical_weightedLaplace_integral_Ioi_of_zero_negative
-- name    : AvramDividend.Classical.weightedLaplace_integral_Ioi_of_zero_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:14:13.143728+00:00
-- url     : https://prove2.me/theorems/c140ad0c-f177-420a-8732-82a0059d0faf
-- title:
--   Full-line weighted Laplace integral reduces to the positive half-line for a function vanishing below zero
-- statement:
--   For any real f vanishing on x<0, the full-line Lebesgue integral of exp(-theta*x) f(x) equals its integral on (0,infinity). The negative half-line contributes zero; the singleton at zero is Lebesgue-null, so the value f(0) is unrestricted. This is crucial for bounded-variation q-scale functions, where W(0) may be strictly positive.
-- source:
--   Elementary support restriction of the q-scale-function Laplace integral in Avram, Palmowski and Pistorius (2007); follows from measure restriction and Mathlib's null-singleton theorem.

import Mathlib

open MeasureTheory Set

namespace AvramDividend.Classical

theorem weightedLaplace_integral_Ioi_of_zero_negative
    (f : ℝ → ℝ) (θ : ℝ)
    (hf : ∀ x : ℝ, x < 0 → f x = 0) :
    (∫ x : ℝ, Real.exp (-(θ * x)) * f x) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x := by sorry

end AvramDividend.Classical
