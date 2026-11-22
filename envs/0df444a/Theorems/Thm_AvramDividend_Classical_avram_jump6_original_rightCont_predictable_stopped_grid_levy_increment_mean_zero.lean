-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_rightCont_predictable_stopped_grid_levy_increment_mean_zero
-- name    : AvramDividend.Classical.avram_jump6_original_rightCont_predictable_stopped_grid_levy_increment_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:35:11.609514+00:00
-- url     : https://prove2.me/theorems/c26cb776-25c7-44d3-9139-4604a0a787bf
-- title:
--   Original finite stopped predictable Lévy increment has mean zero for right-continuous filtration, including initial-event-adapted weights
-- statement:
--   For the original spectrally negative Lévy process and a finite deterministic physical grid, if the stopped predictable coefficient is measurable with respect to the right-continuous original filtration at the cell's left endpoint and integrable, then its product with the next Lévy increment centred by its original expected increment has mean zero. The proof transports the identical original X (including its path, triplet and probability law) to the right-continuous filtration via the Proved filtration-lift theorem, then applies the Proved source predictable-grid martingale centring theorem. This removes the original-versus-right-continuous filtration mismatch for positive-clock and stopped physical-grid verification, without changing the process or post-dividend convention.
-- source:
--   Proved original-X right-continuous filtration lift e58a099d-9977-4265-9e76-7a5f0f6aa758 and Proved stopped original centered cell 00d9de67-d50a-4e9d-95d7-4c63a2180ac3. Supports root expected budget 15815eff and physical grid signed-source candidate 3e0dc3e7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_rightCont_predictable_stopped_grid_levy_increment_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ) (κ : Ω → ℕ)
    (hWPast : Measurable[(𝓕.rightCont) (grid i)]
      (fun ω => if i < κ ω then H i ω else 0))
    (hWI : Integrable
      (fun ω => if i < κ ω then H i ω else 0) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P) :
    (∫ ω, (if i < κ ω then H i ω else 0) *
      (X.X (grid (i + 1)) ω - X.X (grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by sorry
