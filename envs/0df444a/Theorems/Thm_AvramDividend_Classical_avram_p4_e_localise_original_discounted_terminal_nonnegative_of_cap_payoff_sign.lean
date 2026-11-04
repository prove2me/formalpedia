-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:45:44.588207+00:00
-- url     : https://prove2.me/theorems/42338799-ddde-4ad7-9e0a-2f18bea6761e
-- title:
--   Original discounted terminal nonnegative at every ruin/horizon branch from genuine cap payoff sign
-- statement:
--   At any original stopped clock with exact piecewise W, source admissibility and initial-cap assumption ensure ENNReal.ofReal W≤C. If W<0 then source w=0 negative extension cancels; otherwise the explicitly assumed nonnegative cap-range payoff makes w(W)≥0. Multiplication by nonnegative exp discount proves terminal sign, including zero landing and all rightpayment/ruin branches. The cap payoff sign is exposed as a named premise to be established from P4-F hw0/derivative/C² in separate accepted helpers.
-- source:
--   Accepted original cap invariant 0fe5d1ab, Mathlib Real.exp_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original stopped W and negative extension make the discounted terminal nonnegative under cap payoff positivity. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwCapPos : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y) :
    ∀ ω, 0 ≤ Real.exp (-(q * (τ ω : ℝ))) * w (W ω) := by sorry
