-- Prove2me | Theorems.Thm_AvramDividend_Classical_eqOn_Ioi_of_ae_eq_of_continuous_rightContinuous
-- name    : AvramDividend.Classical.eqOn_Ioi_of_ae_eq_of_continuous_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:52:09.12585+00:00
-- url     : https://prove2.me/theorems/ad9fa429-2866-4a6c-b7a1-c6bf49b5972e
-- title:
--   Upgrade positive-halfline a.e. equality using one-sided continuity
-- statement:
--   On the positive real half-line, if f is continuous, g is right-continuous at every positive point, and f=g almost everywhere with respect to Lebesgue measure, then f and g agree at every positive point. Any disagreement persists on a nonempty interval immediately to the right, contradicting almost-everywhere equality.
-- source:
--   One-sided Hausdorff continuity plus positivity of Lebesgue measure on nonempty open intervals. This avoids requiring full continuity of a renewal CDF when upgrading Laplace-transform a.e. identification.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem eqOn_Ioi_of_ae_eq_of_continuous_rightContinuous
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hg : ∀ x : ℝ, 0 < x →
      ContinuousWithinAt g (Ici x) x)
    (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  sorry

end AvramDividend.Classical
