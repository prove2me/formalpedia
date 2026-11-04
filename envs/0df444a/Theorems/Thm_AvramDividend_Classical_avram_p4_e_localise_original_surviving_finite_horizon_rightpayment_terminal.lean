-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_surviving_finite_horizon_rightpayment_terminal
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_surviving_finite_horizon_rightpayment_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:14:29.416209+00:00
-- url     : https://prove2.me/theorems/52e8f4f2-e8fe-4f2a-9f4d-ddb4bffa079f
-- title:
--   Exact original finite-horizon survival gives post-rightdividend W and discounted Term
-- statement:
--   Before the source finite integer horizon, original ruin has not occurred. The exact NNReal truncation is the deterministic horizon and the original terminal switch selects the post-rightpaid reserve, including right-dividend jumps at the horizon. Thus the discounted terminal payoff has the literal source finite-horizon form, without replacing the right limit or discarding a terminal dividend atom.
-- source:
--   Original exact tau/hW/hTerm of canonical 0dda1be7, and pinned ENNReal.min finite horizon coercions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On exact original finite-horizon survival, both source terminal variables use the post-rightpayment finite-horizon reserve. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_surviving_finite_horizon_rightpayment_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W Term : Ω → ℝ) (q : ℝ) (w : ℝ → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, (n : ℝ≥0∞) < ruinTime X x D ω →
      τ ω = (n : ℝ≥0) ∧
      W ω = x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω ∧
      Term ω = Real.exp (-(q * (n : ℝ))) *
        w (x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω) := by sorry
