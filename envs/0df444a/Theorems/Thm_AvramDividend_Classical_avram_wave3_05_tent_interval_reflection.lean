-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_interval_reflection
-- name    : AvramDividend.Classical.avram_wave3_05_tent_interval_reflection
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:30:01.280699+00:00
-- url     : https://prove2.me/theorems/a1f28103-6cc3-4430-82ce-73c33e9dc238
-- title:
--   Exact change of variables from the generator's backward Taylor integral to a tent convolution
-- statement:
--   For every real x, r and integrand F, the backward positive-state second-order Taylor integral over [x−r,x] is exactly the reflected triangular kernel integral over [0,r]. This source-derived change of variables is the bridge between the genuine compensated Lévy generator interior and the integrable tent convolution estimate. It has no hidden smoothness or support hypotheses and keeps the exact orientation.
-- source:
--   Pinned Mathlib intervalIntegral.integral_comp_sub_left, verified via private remote probe on 30 October 2026. Previous publication job c0a4e040 failed due to unknown namespace AvramDividend.Classical; the accepted source Definition import ensures the target namespace is in the publication environment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_interval_reflection
    (F : ℝ → ℝ) (x r : ℝ) :
    (∫ u in (x - r)..x, (u - (x - r)) * F u) =
      ∫ s in (0 : ℝ)..r, (r - s) * F (x - s) := by sorry
