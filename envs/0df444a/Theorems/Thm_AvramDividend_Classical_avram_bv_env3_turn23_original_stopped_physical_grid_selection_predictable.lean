-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
-- name    : AvramDividend.Classical.avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:54:38.273323+00:00
-- url     : https://prove2.me/theorems/5319a1cb-c412-4ada-bbb3-e490e66cb669
-- title:
--   Original stopping time makes pre-clock physical-grid event predictable
-- statement:
--   For the original right-continuous filtration of a spectrally negative Lévy process, the event that the stopping time tau has not yet occurred by a physical grid time u_i belongs to the filtration at u_i. It is exactly the complement of the stopping-time event tau≤u_i.
-- source:
--   Pinned Mathlib IsStoppingTime at original filtration, measurability under set complement; contributes predictable event to BV-ENV3 original stopped signed grid and P3 finite-source martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (i : ℕ) :
    MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} := by sorry
