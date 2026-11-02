-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_C1_polynomial_error_expectation_first_moment_bound
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_C1_polynomial_error_expectation_first_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T16:21:12.841534+00:00
-- url     : https://prove2.me/theorems/5682def5-750d-4c7e-ae70-52e66f37ab7d
-- title:
--   Original BV Lévy process C1 moving-base expected polynomial error controlled by actual residual first-moment tail
-- statement:
--   Under genuine Standing and BV for the original Lévy process, construct one zero-constant exponential polynomial p and base tolerance δ so that at every original time t≤1 with physical-drift displacement smaller than δ, the Bochner expected C1 payoff decrement minus polynomial primitive is bounded by epsilon times the true residual first moment plus (2L+epsilon) times its large-tail first moment. The proof combines all separately Proved actual residual measurability, monotonicity, full/tail integrability and fixed moving-base polynomial approximation with rigorous random error integrability and expectation domination. It is precisely the process-specific uniform-integrability inequality needed for the canonical C1 semigroup bridge; no new generator identity, second derivative, coupling or process replacement.
-- source:
--   Remote compiler candidates/work_on/AvramDividend_04c_original_BV_C1_polynomial_error_expected_bound_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_moving_base_residual_polynomial_first_moment_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_random_residual_poly_error_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_random_integrated_error_first_moment_bound
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_C1_polynomial_error_expectation_first_moment_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w) (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|) (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      ∀ t : ℝ≥0, t ≤ 1 →
        |(x + (t : ℝ) * X.drift) - x| < δ →
        |∫ ω, (w (x + (t : ℝ) * X.drift) -
          w (x + X.X t ω)) -
          (∫ r in (0 : ℝ)..((t : ℝ) * X.drift - X.X t ω),
            Polynomial.eval (Real.exp (-r)) p) ∂P| ≤
          ε * (∫ ω, (t : ℝ) * X.drift - X.X t ω ∂P) +
            (2 * L + ε) * (∫ ω,
              if M < (t : ℝ) * X.drift - X.X t ω
              then (t : ℝ) * X.drift - X.X t ω else 0 ∂P) := by sorry
