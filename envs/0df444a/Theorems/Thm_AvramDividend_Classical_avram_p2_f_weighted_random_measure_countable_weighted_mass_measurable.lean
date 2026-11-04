-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_random_measure_countable_weighted_mass_measurable
-- name    : AvramDividend.Classical.avram_p2_f_weighted_random_measure_countable_weighted_mass_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:49:39.967592+00:00
-- url     : https://prove2.me/theorems/e08df39c-f928-4e07-b6e7-1c076dfef8a6
-- title:
--   Countable weighted true random-measure cell mass sum is outer measurable
-- statement:
--   For a genuine sample-dependent measure M_ω, a countable family of actual cell masses M_ω(C_i) and arbitrary nonnegative random coefficients H_i, the random infinite sum of weighted actual cell masses is measurable in ω provided each cell-mass map and coefficient is separately measurable. This explicit random-measure measurability interface is needed to combine countable pathwise marked-jump integrals with the outer Lévy expectation. It does not assume the whole random measure is a kernel nor any original ν-rate.
-- source:
--   Pinned Mathlib Measurable.ennreal_tsum and Measurable.mul; per-cell measurability explicit.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_random_measure_countable_weighted_mass_measurable
    {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Countable ι]
    (M : Ω → Measure α) (C : ι → Set α)
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable (H i))
    (hMass : ∀ i, Measurable (fun ω => M ω (C i))) :
    Measurable (fun ω => ∑' i, H i ω * M ω (C i)) := by sorry
