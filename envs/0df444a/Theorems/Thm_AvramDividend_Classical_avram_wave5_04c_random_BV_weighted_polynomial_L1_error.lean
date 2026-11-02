-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_random_BV_weighted_polynomial_L1_error
-- name    : AvramDividend.Classical.avram_wave5_04c_random_BV_weighted_polynomial_L1_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:35:20.379417+00:00
-- url     : https://prove2.me/theorems/a0966dbc-34c9-47c7-af95-1ec83273e6d9
-- title:
--   Bochner L1 transfer of BV-weighted exponential polynomial errors for integrable random residuals
-- statement:
--   For a measurable a.e. nonnegative integrable random variable R and a first-moment-integrable truncated tail, integrate a weighted pointwise C1 polynomial error. Use 1-exp(-R)≤R, continuity of the payoff and polynomial to establish measurability, integrable dominance to justify Bochner interchange, and the triangle/integral inequality to bound the absolute expected error by the first moment plus distant tail. This is the actual stochastic uniform-integrability estimate applied to the original BV Lévy residual, not an assumed generator identity.
-- source:
--   Mathlib dominated Bochner integrability, add_one_le_exp, and integral_mono_ae.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_04c_random_BV_weighted_polynomial_L1_error {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R : Ω → ℝ) (hRm : Measurable R)
    (hRnn : ∀ᵐ ω ∂P, 0 ≤ R ω) (hRi : Integrable R P)
    (M ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hTail : Integrable (fun ω => if M < R ω then R ω else 0) P)
    (f : ℝ → ℝ) (hf : Continuous f) (Q : Polynomial ℝ)
    (hPoint : ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - f r| ≤
      ε * (1 - Real.exp (-r)) +
        (if M < r then K * r else 0)) :
    |∫ ω, f (R ω) - Polynomial.eval (Real.exp (-R ω)) Q ∂P| ≤
      ε * (∫ ω, R ω ∂P) +
        K * (∫ ω, if M < R ω then R ω else 0 ∂P) := by sorry
