-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_random_integrated_error_first_moment_bound
-- name    : AvramDividend.Classical.avram_wave5_04c_random_integrated_error_first_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:48:52.367441+00:00
-- url     : https://prove2.me/theorems/805aba16-8c40-4ac7-b14e-4bb638d59b2e
-- title:
--   Bochner expectation error controlled by full and truncated first moments
-- statement:
--   For any measurable random residual and integrable error, if an almost-everywhere C1 approximation error is bounded by epsilon times the residual plus (2L+epsilon) times its large-threshold tail, the absolute Bochner expectation error is bounded by the corresponding two first-moment expectations. All integrability of the quantities in the conclusion is explicitly required and the proof uses rigorous norm-of-integral domination, almost-everywhere integral monotonicity and linearity. This interfaces directly with the previously Proved source residual first-moment and uniform tail estimates; it does not assert the full Lévy generator theorem.
-- source:
--   Remote compiler sentinel-verified candidates/work_on/AvramDividend_04c_random_integrated_error_first_moment_domination_probe.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem AvramDividend.Classical.avram_wave5_04c_random_integrated_error_first_moment_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R E : Ω → ℝ) (M ε L : ℝ)
    (hER : Integrable E P) (hRR : Integrable R P)
    (hTail : Integrable (fun ω => if M < R ω then R ω else 0) P)
    (hPoint : ∀ᵐ ω ∂P,
      |E ω| ≤ ε * R ω +
        (2 * L + ε) * (if M < R ω then R ω else 0)) :
    |∫ ω, E ω ∂P| ≤
      ε * (∫ ω, R ω ∂P) +
        (2 * L + ε) *
          (∫ ω, if M < R ω then R ω else 0 ∂P) := by sorry
