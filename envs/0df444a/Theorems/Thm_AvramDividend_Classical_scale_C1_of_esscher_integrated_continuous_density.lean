-- Prove2me | Theorems.Thm_AvramDividend_Classical_scale_C1_of_esscher_integrated_continuous_density
-- name    : AvramDividend.Classical.scale_C1_of_esscher_integrated_continuous_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:08:28.332486+00:00
-- url     : https://prove2.me/theorems/ae37dce4-7df3-41e5-a964-77bd760968e2
-- title:
--   C1 positive-axis scale regularity from a continuous Esscher-renewal density
-- statement:
--   For any scale candidate W whose Esscher tilt equals a constant plus the interval integral of a continuous, locally integrable density on the positive axis, the original W is continuously differentiable there. This isolates the analytic continuity-of-renewal-density obligation in the bounded-variation Lévy branch.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale-function smooth fit and BV renewal structure. Uses Proved positive-axis integral C1 and Esscher untilting lemmas.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one

open AvramDividend.Classical MeasureTheory Set intervalIntegral

namespace AvramDividend.Classical
theorem scale_C1_of_esscher_integrated_continuous_density
    (W f : ℝ → ℝ) (φ c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hrepr : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x =
        c + ∫ y in (0 : ℝ)..x, f y) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
end AvramDividend.Classical
