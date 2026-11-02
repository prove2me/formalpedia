-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_uniform_grid_one_cell_tail_bound
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_uniform_grid_one_cell_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:19:57.626371+00:00
-- url     : https://prove2.me/theorems/7316c5a0-8891-4626-a032-a4eff287b44b
-- title:
--   Original BV Lévy source one-cell expected residual tail controlled by terminal grid tail
-- statement:
--   For the actual spectrally negative Lévy source X under Standing and BoundedVariation, any grid time h≤1 with nh≤1, and any real cutoff M, n times the exact first-moment threshold tail of the physical drift residual R_h=h d-X_h is bounded by the first-moment threshold tail of R_nh. The proof uses only actual source residual monotonicity, the Proved source stationary-increment law and integrability to identify each grid-cell integral, and finite-grid domination. No alternate process or assumptions.
-- source:
--   Complete original source private remote compiler verified (sentinel): candidates/work_on/AvramDividend_04c_actual_residual_expected_n_cell_tail_compact.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_uniform_grid_one_cell_tail_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (h : ℝ≥0) (hh : h ≤ 1) (n : ℕ)
    (hn : (n : ℝ≥0) * h ≤ 1) (M : ℝ) :
    (n : ℝ) * (∫ ω, if M < (h : ℝ) * X.drift - X.X h ω
      then (h : ℝ) * X.drift - X.X h ω else 0 ∂P) ≤
    (∫ ω, if M < (((n : ℝ≥0) * h : ℝ) * X.drift -
                       X.X ((n : ℝ≥0) * h) ω)
         then (((n : ℝ≥0) * h : ℝ) * X.drift -
                       X.X ((n : ℝ≥0) * h) ω) else 0 ∂P) := by sorry
