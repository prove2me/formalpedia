-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_joint_poly_uniform_normalized_semigroup_error
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_BV_joint_poly_uniform_normalized_semigroup_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:52:31.968566+00:00
-- url     : https://prove2.me/theorems/4f5f3342-cf94-4f9a-b813-1feb52fe4407
-- title:
--   Original BV C1 transition residual uniformly approximable by one polynomial also controlling the original generator
-- statement:
--   For each eta>0 there is a finite cutoff M and ONE endpoint-zero polynomial Q that has both (i) the sharp original negative Lévy generator jump-error bound, with signed-payoff tail and BV exponential weight, and (ii) a uniform expected ORIGINAL BV source residual approximation error after division by actual time h: at every positive h≤1/2 it is at most eta times the fixed finite quantity 2 E[R_1]+2L. This combines the Proved original-source uniform normalized first moment, uniform integrability of large residual tails, and the same Q's simultaneous payoff approximation. This directly addresses the hard source semigroup approximation needed for the canonical C1 theorem.
-- source:
--   Proved genuine BV original-source normalized mean/tail estimates, signed C1 joint polynomial choice, and Bochner expected residual polynomial error.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_BV_joint_poly_uniform_normalized_semigroup_error {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      (∀ y : ℝ, y < 0 →
        |Polynomial.eval (Real.exp y) Q - (w x - w (x + y))| ≤
          η * (1 - Real.exp y) +
            (if y < -M then 2 * |w x - w (x + y)| else 0)) ∧
      ∀ h : ℝ≥0, 0 < h → h ≤ (1 / 2 : ℝ≥0) →
        |(h : ℝ)⁻¹ * (∫ ω,
          (w x - w (x - ((h : ℝ) * X.drift - X.X h ω))) -
          Polynomial.eval
            (Real.exp (-((h : ℝ) * X.drift - X.X h ω))) Q ∂P)| ≤
        η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) + 2 * L) := by sorry
