-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:34:14.95436+00:00
-- url     : https://prove2.me/theorems/d93b8897-a415-4e6c-abdc-70f27dae0a7e
-- title:
--   Original stopped physical grid count is predictable at each genuine left-grid time
-- statement:
--   For a genuinely stopped original Lévy clock and any monotone deterministic physical mesh, the event that the count of pre-stop grid points exceeds i is measurable in the right-continuous filtration at the i-th left endpoint. This instantiates the adapted-prefix hypothesis in the random stopped-martingale reduction with a clock-derived index.
-- source:
--   Accepted turn23 original stopping selection and turn12 stopped prefix-card combinatorial reduction 665ec4c6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    ∀ i, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card} := by sorry
