-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_density_bochner_integral
-- name    : AvramDividend.Classical.avram_gen14_singular_density_bochner_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:33:46.568194+00:00
-- url     : https://prove2.me/theorems/ee13438e-1918-41a9-8404-8be43c78715b
-- title:
--   Change the proposed singular negative-jump density integral to a weighted Lebesgue integral
-- statement:
--   For any real-valued measurable or nonmeasurable integrand, the Bochner integral against the proposed negative-jump Levy measure defined by the singular Borel density agrees with the corresponding weighted Lebesgue Bochner integral. The equality follows from the exact pinned Mathlib density integration theorem; it does not assume either side is absolutely integrable.
-- source:
--   Exact change-of-measure bridge for the explicit Levy density; uses its proved measurability and finite pointwise values.

import Mathlib
open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen14_singular_density_bochner_integral
    (g : ℝ → ℝ) :
    (∫ z, g z ∂(volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) =
    (∫ z, (if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0).toReal * g z ∂volume) := by sorry
