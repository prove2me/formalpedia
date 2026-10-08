-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
-- name    : AvramDividend.Classical.continuous_rightContinuous_Ioi_eq_of_laplace_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T23:11:18.849249+00:00
-- url     : https://prove2.me/theorems/d0a7b4b9-cfbf-43d2-be85-bf45b3ad503a
-- title:
--   Laplace uniqueness with a continuous function and a right-continuous comparator
-- statement:
--   A continuous nonnegative function and an a.e.-measurable right-continuous nonnegative function on the positive half-line agree pointwise when their Laplace transforms agree for every sufficiently large parameter.
-- source:
--   Adaptation of the accepted continuous Laplace-uniqueness proof using a.e. density identification followed by the right-continuous pointwise upgrade.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace AvramDividend.Classical

theorem continuous_rightContinuous_Ioi_eq_of_laplace_eq
    (f g : ℝ → ℝ) (b : ℝ)
    (hfcont : ContinuousOn f (Ioi 0))
    (hgright : ∀ x : ℝ, 0 < x → ContinuousWithinAt g (Ici x) x)
    (hgmeas : AEMeasurable g (volume.restrict (Ioi 0)))
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
