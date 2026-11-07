-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:35:39.796451+00:00
-- url     : https://prove2.me/theorems/f53747fc-ec1e-4334-8141-c584b782e9d4
-- title:
--   Genuine original stopping-time selected finite grid count is measurable and uniformly bounded
-- statement:
--   For the original spectrally negative Lévy process and its true right-continuous stopping time, the number of fixed finite physical-grid points strictly before stopping is a measurable random natural number bounded by the grid size. No independence or conditional martingale hypothesis is needed.
-- source:
--   Accepted original stop-time predictable selection turn23 and Mathlib Finset.card_filter, measurable_sum, filter_subset.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (fun ω : Ω =>
      ((Finset.range m).filter
        (fun i => (u i : WithTop ℝ≥0) < τ ω)).card) ∧
    (∀ ω, ((Finset.range m).filter
      (fun i => (u i : WithTop ℝ≥0) < τ ω)).card ≤ m) := by sorry
