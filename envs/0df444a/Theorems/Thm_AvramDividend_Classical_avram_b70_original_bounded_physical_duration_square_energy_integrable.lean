-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b70_original_bounded_physical_duration_square_energy_integrable
-- name    : AvramDividend.Classical.avram_b70_original_bounded_physical_duration_square_energy_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:40:46.529766+00:00
-- url     : https://prove2.me/theorems/1988e083-3abb-409d-bc7f-6f9d7dab4c1f
-- title:
--   Original bounded physical stopped-grid elapsed duration square energy is integrable
-- statement:
--   For the original spectrally negative Levy process, any finite grid of original bounded random clock endpoints with measurable square-duration total has an integrable squared duration sum; the deterministic bound is cardinality times T squared.
-- source:
--   Original SpectrallyNegativeLevy probability assumption; NNReal truncated subtraction tsub_le_self and Integrable.of_bound at pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b70_original_bounded_physical_duration_square_energy_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hMeas : AEStronglyMeasurable (fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P)
    (hBound : ∀ ω i, i ∈ S → t i ω ≤ T) :
    Integrable (fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P := by sorry
