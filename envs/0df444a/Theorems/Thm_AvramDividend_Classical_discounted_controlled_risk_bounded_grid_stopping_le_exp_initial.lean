-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_controlled_risk_bounded_grid_stopping_le_exp_initial
-- name    : AvramDividend.Classical.discounted_controlled_risk_bounded_grid_stopping_le_exp_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:31:19.394767+00:00
-- url     : https://prove2.me/theorems/8a08cf22-bfa3-43fd-9095-ed9fc448a0ae
-- title:
--   Any bounded natural-grid stopping time of controlled discounted exponential has expectation at most its initial value
-- statement:
--   For any dividend strategy, θ≥0 and q≥ψθ, the discounted exponential of the actual reserve x+X−D at any bounded stopping time of the sampled filtration has expectation ≤exp(θx). This extends the previously sampled first-ruin bound to arbitrary bounded stopping times, relying on the controlled exponential supermartingale, sampling, and the already accepted generic bounded optional-stopping theorem.
-- source:
--   AvramDividend.Classical.discounted_controlled_risk_exponential_supermartingale, supermartingale_sample_nat, supermartingale_expected_stoppedValue_antitone_nat; exact X0 and D0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_controlled_risk_bounded_grid_stopping_le_exp_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime 𝓖 τ)
    (N : ℕ) (hbdd : ∀ ω, τ ω ≤ (N : WithTop ℕ)) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * riskProcess X x D (n : ℝ≥0) ω -
          ((n : ℝ≥0) : ℝ) * q))
      τ ω ∂P) ≤ Real.exp (θ * x) := by sorry
