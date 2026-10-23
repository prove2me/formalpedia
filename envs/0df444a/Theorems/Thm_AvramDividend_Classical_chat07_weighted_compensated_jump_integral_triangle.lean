-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_weighted_compensated_jump_integral_triangle
-- name    : AvramDividend.Classical.chat07_weighted_compensated_jump_integral_triangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:02:52.804996+00:00
-- url     : https://prove2.me/theorems/769423b7-f933-4bce-b2dc-310a7b9f10d8
-- title:
--   Integrated triangle bound for each compensated negative jump
-- statement:
--   For a monotone real function and nonnegative negative-jump magnitude, assume integrability over positive reserves of the weighted compensated absolute kernel, its absolute shift decrement, and its ordinary derivative term. Then the first integral is bounded by the sum of the shift-decrement integral and jump magnitude times the derivative integral. This is the exact integrated triangle estimate needed before using the scale shift min-bound and the BV jump first moment.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat07_weighted_compensated_jump_integral_triangle
    (W : ℝ → ℝ) (hW : Monotone W)
    (θ r : ℝ) (hr : 0 ≤ r)
    (hker : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |W (x-r) - W x + r * deriv W x|) (Ioi (0 : ℝ)))
    (hshift : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |W x - W (x-r)|) (Ioi (0 : ℝ)))
    (hderiv : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
      (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        |W (x-r) - W x + r * deriv W x|) ≤
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        |W x - W (x-r)|) +
      r * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv W x) := by sorry
