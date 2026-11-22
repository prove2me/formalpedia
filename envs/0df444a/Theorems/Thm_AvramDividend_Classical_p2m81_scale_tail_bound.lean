-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_scale_tail_bound
-- name    : AvramDividend.Classical.p2m81_scale_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T09:34:20.315507+00:00
-- url     : https://prove2.me/theorems/f66e3f14-314a-4e9b-bdad-44d6ab63eae1
-- title:
--   Scale tail integral bound by Laplace shift
-- statement:
--   For nonnegative W on (0,oo), the tail Laplace integral at parameter beta over (a,oo) is at most exp(-(beta-beta0)*a)*K whenever the beta0 full integral is at most K. Helper D2 for parent fc6b315a: congruence wrapper translating the IsScaleFunction exp normal form exp(-(b*x)) to the (-b)*x form of Proved public laplace_tail_shift_bound, then chaining monotonicity from (a,oo) to (0,oo).
-- source:
--   Decomposition child D2 of fc6b315a. Uses only Proved public laplace_tail_shift_bound (8d8b0521) at pinned rev; statement is pure analysis.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_scale_tail_bound (W : ℝ → ℝ) (a β0 β K : ℝ) (ha : 0 < a) (hβ : β0 ≤ β)
    (hWnn : ∀ x : ℝ, 0 < x → 0 ≤ W x)
    (hint0 : IntegrableOn (fun x : ℝ => Real.exp (-(β0 * x)) * W x) (Ioi (0:ℝ)))
    (hint1 : IntegrableOn (fun x : ℝ => Real.exp (-(β * x)) * W x) (Ioi a))
    (hK : (∫ x in Ioi (0:ℝ), Real.exp (-(β0 * x)) * W x) ≤ K) :
    (∫ x in Ioi a, Real.exp (-(β * x)) * W x) ≤ Real.exp (-(β - β0) * a) * K := by sorry
