-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_normalized_C1_polynomial_error_uniform
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_normalized_C1_polynomial_error_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:37:06.917448+00:00
-- url     : https://prove2.me/theorems/8dba95d0-fd8a-40ce-95e8-c0ec8fd11b9f
-- title:
--   Uniform inverse-time C1 polynomial approximation error for the original BV Lévy process
-- statement:
--   For each positive approximation error, choose one exponential polynomial and one drift-neighbourhood so that the original BV Lévy process expected moving-base payoff approximation has a uniform small inverse-time error, bounded by epsilon times its fixed terminal first-moment budget. This proves the normalized semigroup-side C1 approximation using the genuine process, integrability, and verified uniform residual-tail domination.
-- source:
--   Direct logical consequence of the Proved original-process expected polynomial error bound 5682def5, original normalized first-moment bound 741b9ad7, and normalized large-residual tail uniform vanishing 691bd8ab.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_C1_polynomial_error_expectation_first_moment_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_normalized_C1_polynomial_error_uniform
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      ∀ h : ℝ≥0, 0 < h → h ≤ (1 / 2 : ℝ≥0) →
        |(x + (h : ℝ) * X.drift) - x| < δ →
        |(h : ℝ)⁻¹ * (∫ ω,
          (w (x + (h : ℝ) * X.drift) - w (x + X.X h ω)) -
            (∫ r in (0 : ℝ)..((h : ℝ) * X.drift - X.X h ω),
              Polynomial.eval (Real.exp (-r)) p) ∂P)| ≤
        ε * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) +
          2 * L + ε) := by sorry
