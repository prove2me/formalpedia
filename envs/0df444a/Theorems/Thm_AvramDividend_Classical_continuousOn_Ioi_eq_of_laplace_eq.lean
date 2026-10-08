-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
-- name    : AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T19:25:00.552737+00:00
-- url     : https://prove2.me/theorems/fdbf4813-b5d2-4b56-8029-649f638988c1
-- title:
--   Uniqueness of continuous nonnegative functions from a Laplace half-line
-- statement:
--   Let f and g be nonnegative continuous real-valued functions on (0,∞). Suppose there is a real threshold b such that for every Laplace parameter θ>b, both exponentially weighted functions exp(-θx)f(x) and exp(-θx)g(x) are integrable on (0,∞), and their integrals are equal. Then f(x)=g(x) for every x>0. The intended proof fixes B>b, regards exp(-Bx)f(x) and exp(-Bx)g(x) as densities of finite measures, identifies those measures from their moment-generating functions on a left half-plane, recovers almost-everywhere equality of densities, and upgrades it to pointwise equality by continuity.
-- source:
--   Standard uniqueness theorem for Laplace transforms of continuous nonnegative functions. Formal route uses pinned Mathlib ProbabilityTheory complexMGF analyticity, MeasureTheory.withDensity_eq_iff_of_sigmaFinite, and Proved AvramDividend.Classical.finiteMeasures_eq_of_complexMGF_eq_on_real_Iio (3c031447-1ce2-436e-933b-fdf2716c0fc1).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
open MeasureTheory Filter Set Topology
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace AvramDividend.Classical

/-- Two nonnegative continuous functions on the positive half-line agree pointwise
if their Laplace transforms agree for every sufficiently large parameter. -/
theorem continuousOn_Ioi_eq_of_laplace_eq
    (f g : ℝ → ℝ) (b : ℝ)
    (hfcont : ContinuousOn f (Ioi 0))
    (hgcont : ContinuousOn g (Ioi 0))
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * g x) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * f x =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  sorry

end AvramDividend.Classical
