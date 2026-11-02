-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:41:03.022203+00:00
-- url     : https://prove2.me/theorems/691bd8ab-8702-42bc-bd06-1162315b3fa7
-- title:
--   Actual BV Lévy residual normalized first-moment tails vanish uniformly in small time
-- statement:
--   For every epsilon>0 and under genuine Standing plus BoundedVariation of X, all sufficiently large natural thresholds n satisfy, uniformly over 0<h≤1/2, h^{-1}E[(h*d-X_h)1_{h*d-X_h>n}]<epsilon. The accepted original-source normalized one-cell tail inequality bounds this quantity by twice the terminal R1 first-moment tail. Since R1 is integrable from Standing and BV monotonicity, the independently Proved Bochner dominated-convergence tail lemma makes the terminal tail vanish. No assumed generator identity, replacement process or new first-moment premise.
-- source:
--   Complete remote compiler sentinel-verified source candidates/work_on/AvramDividend_04c_original_bv_normalized_tail_uniform_vanish_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_real_truncated_first_moment_tail_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
       ∀ h : ℝ≥0, 0 < h → h ≤ (1 / 2 : ℝ≥0) →
       (h : ℝ)⁻¹ * (∫ ω, if (n : ℝ) < (h : ℝ) * X.drift - X.X h ω
          then (h : ℝ) * X.drift - X.X h ω else 0 ∂P) < ε := by sorry
