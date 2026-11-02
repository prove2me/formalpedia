-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:40:46.678932+00:00
-- url     : https://prove2.me/theorems/741b9ad7-417b-44d1-ae97-78848a76501d
-- title:
--   Original BV Lévy residual expected first moment has a uniform inverse-time bound
-- statement:
--   For the original BV Lévy source under Standing, every 0<h≤1/2 satisfies h^{-1}E[h*d-X_h]≤2E[d-X_1]. Actual source physical-drift deficit is nonnegative a.e by Proved BV residual monotonicity; threshold M=0 of the Proved one-cell normalized first-moment tail inequality then equals the whole first moment on both sides. This supplies the 1/h uniform first-moment bound needed for globally Lipschitz C1 approximations.
-- source:
--   Complete remote compiler sentinel-verified source candidates/work_on/AvramDividend_04c_actual_bv_residual_normalized_full_mean_bound_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (h : ℝ≥0) (hhpos : 0 < h) (hhhalf : h ≤ (1 / 2 : ℝ≥0)) :
    (h : ℝ)⁻¹ * (∫ ω, (h : ℝ) * X.drift - X.X h ω ∂P)
      ≤ 2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) := by sorry
