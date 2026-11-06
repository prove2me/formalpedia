-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn27_original_stopping_clock_condexp_selected_cell_mean_zero
-- name    : AvramDividend.Classical.avram_bv_env3_turn27_original_stopping_clock_condexp_selected_cell_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:02:53.725288+00:00
-- url     : https://prove2.me/theorems/d1eba19a-1123-466a-9a30-bdba8d236d31
-- title:
--   Original stopping-clock selected conditional martingale cell integral is zero
-- statement:
--   For a genuine original Lévy stopping clock τ, each original source increment M_i with integrable conditional zero mean on the right-continuous past at physical grid time u_i has zero mean after selection by u_i<τ. The event is predictable because it is the complement of {τ≤u_i}.
-- source:
--   Accepted turn23 original stopping-time selection predictability and pinned Mathlib setIntegral_condExp, integral_indicator, ae_restrict_of_ae. A direct reduction step to the original signed stopped finite-grid budget turn24.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn27_original_stopping_clock_condexp_selected_cell_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (M : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0) :
    ∀ i, (∫ ω, if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0 ∂P)
      = 0 := by sorry
