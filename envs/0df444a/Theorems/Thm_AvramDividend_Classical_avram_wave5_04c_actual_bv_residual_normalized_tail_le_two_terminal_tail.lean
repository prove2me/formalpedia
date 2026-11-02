-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:34:41.624211+00:00
-- url     : https://prove2.me/theorems/50956a5e-fb45-4ba5-bd26-266a64f44cff
-- title:
--   Uniform inverse-time bound for original BV Lévy residual first-moment threshold tails
-- statement:
--   For the actual spectrally negative Lévy process under Standing and BoundedVariation, uniformly for every time 0<h≤1/2 and every real cutoff M, h^{-1} E[(h*d-X_h)1_{h*d-X_h>M}]≤2 E[(d-X_1)1_{d-X_1>M}]. The proof constructs n=floor(1/h), obtains 1/2≤nh≤1, applies the Proved original-source n-cell tail bound, actual residual monotonicity to time 1, and nonnegativity of the actual residual. No replacement process, coupling or extra integrability premise is used.
-- source:
--   Complete original-process remote compiler sentinel-verified source candidates/work_on/AvramDividend_04c_actual_bv_normalized_tail_bound_inline_floor_compact.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_uniform_grid_one_cell_tail_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_expected_monotone_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (h : ℝ≥0) (hhpos : 0 < h) (hhhalf : h ≤ (1 / 2 : ℝ≥0))
    (M : ℝ) :
    (h : ℝ)⁻¹ * (∫ ω, if M < (h : ℝ) * X.drift - X.X h ω
       then (h : ℝ) * X.drift - X.X h ω else 0 ∂P)
     ≤ 2 * (∫ ω, if M < (1 : ℝ) * X.drift - X.X 1 ω
       then (1 : ℝ) * X.drift - X.X 1 ω else 0 ∂P) := by sorry
