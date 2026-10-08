-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_exponential_withDensity_eq
-- name    : AvramDividend.Classical.continuousOn_Ioi_eq_of_exponential_withDensity_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T19:26:45.829235+00:00
-- url     : https://prove2.me/theorems/ad0d45c8-f9ee-4c01-8ce9-c215629ef511
-- title:
--   Continuous positive-halfline densities are identified by equal exponential withDensity measures
-- statement:
--   Let f and g be continuous and nonnegative on (0,∞), and fix a real exponential tilt B. If the two measures on (0,∞) with densities exp(-Bx)f(x) and exp(-Bx)g(x) with respect to Lebesgue measure are equal, then f(x)=g(x) for every x>0. Equality of withDensity measures gives almost-everywhere equality of the nonnegative ENNReal densities; positivity of the exponential factor cancels the common tilt, and continuity upgrades almost-everywhere equality to pointwise equality.
-- source:
--   Pinned Mathlib MeasureTheory.withDensity_eq_iff_of_sigmaFinite, MeasureTheory.eqOn_open_of_ae_eq, ENNReal.ofReal_eq_ofReal_iff, and Real.exp_pos.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace AvramDividend.Classical

/-- Equality of exponentially weighted density measures identifies continuous
nonnegative functions pointwise on the positive half-line. -/
theorem continuousOn_Ioi_eq_of_exponential_withDensity_eq
    (f g : ℝ → ℝ) (B : ℝ)
    (hfcont : ContinuousOn f (Ioi 0))
    (hgcont : ContinuousOn g (Ioi 0))
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hfdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x))
      (volume.restrict (Ioi 0)))
    (hgdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x))
      (volume.restrict (Ioi 0)))
    (hmeas :
      (volume.restrict (Ioi 0)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x)) =
        (volume.restrict (Ioi 0)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x))) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  sorry

end AvramDividend.Classical
