-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_zero_clock_rightpayment_term_exact
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_zero_clock_rightpayment_term_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:10:53.500842+00:00
-- url     : https://prove2.me/theorems/858cdf8b-d383-4dfc-9eeb-8b2b959a311c
-- title:
--   True original zero clock terminal preserves right-dividend payment in W and discounted Term
-- statement:
--   At the genuine original stopped clock zero, the terminal reserve is x minus the right-limit dividend at time zero, using the Lévy X(0)=0 property. The zero discount exponential makes the terminal payoff exactly w of that post-payment reserve. This retains the original right-payment atom and avoids replacing it with D(0) or a killed reserve.
-- source:
--   Exact canonical 0dda1be7 hW and hTerm source branches, SpectrallyNegativeLevy.X_zero and the right-limit dividend definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At the original stopped clock zero, W and the discounted terminal retain the actual time-zero right-dividend payment. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_zero_clock_rightpayment_term_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (q : ℝ) (w : ℝ → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, τ ω = 0 →
      W ω = x - rightLimit D 0 ω ∧
      Term ω = w (x - rightLimit D 0 ω) := by sorry
