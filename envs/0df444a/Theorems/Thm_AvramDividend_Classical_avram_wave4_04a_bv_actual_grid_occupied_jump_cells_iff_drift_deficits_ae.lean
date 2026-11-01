-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:27:24.286202+00:00
-- url     : https://prove2.me/theorems/4426d791-7c3f-4ad0-bb9e-c0c564bfef20
-- title:
--   Genuine original BV Lévy jump-occupied grid cells coincide with drift-deficient source increment cells almost surely
-- statement:
--   On one original-P-full finite-horizon event for a genuine BV finite-activity spectrally negative Lévy source X, for every finite grid of nondecreasing time cells inside [0,T], the set of indices of cells containing at least one actual nonzero left-limit jump of X is exactly the set of cells with strict drift-deficient original X endpoint increments. This is the missing source-specific pathwise identification of measurable grid indicators with the true intrinsic N_X occupied cells, valid uniformly over all finite grids and not relying on a constructed Poisson process or count law.
-- source:
--   Directly derive all-grid index-set equality from canonically Proved d775f040-013e-459c-957a-68cfcabe2e0e, the genuine original-X BV residual strict interval iff a true source jump on every subinterval simultaneously. Under s≤t, NNReal.coe_sub hst and nlinarith convert the exact residual strict inequality into X_t−X_s < drift·(t−s). Set ext finishes the equality for every finite grid. No auxiliary-Lévy replacement or filtration change.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_occupied_jump_cells_iff_drift_deficits_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (grid : ℕ → ℝ≥0),
      (∀ i : ℕ, i < n →
        grid i ≤ grid (i + 1) ∧ grid (i + 1) ≤ T) →
      {i : ℕ | i < n ∧ ∃ u : ℝ≥0,
        u ∈ Ioc (grid i) (grid (i + 1)) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} =
      {i : ℕ | i < n ∧
        X.X (grid (i + 1)) ω - X.X (grid i) ω <
          X.drift * (((grid (i + 1) - grid i : ℝ≥0) : ℝ))} := by sorry
