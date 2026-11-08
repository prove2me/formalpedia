-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_cell_product_filtration_measurable
-- name    : AvramDividend.Classical.avram_route_runner_g_original_cell_product_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:24:09.858832+00:00
-- url     : https://prove2.me/theorems/8ad9d684-0236-476c-899c-8c79e1397cc7
-- title:
--   Original half-open marked cell product is measurable in its endpoint filtration
-- statement:
--   For any two deterministic times s ≤ t ≤ 1, the product of exponential strictly negative cutoff jumps on the actual Lévy process over (s,t] is measurable in the source filtration at t. Express the cell product as the quotient of nonzero adapted prefix marked products and use finite marked-time set stability.
-- source:
--   AVRAM Route Runner G, source-exact filtration measurability needed to prove 8b604395 independence of equal cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_finset_stable
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_prefix_product_filtration_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_g_original_cell_product_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ 1) (k : ℕ) :
    Measurable[𝓕 t] (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
