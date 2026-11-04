-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_ruin_terminal_zero_landing_vs_overshoot
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_terminal_zero_landing_vs_overshoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:48:23.815072+00:00
-- url     : https://prove2.me/theorems/7fddba07-78b0-4f15-a3b0-4be5f6b38146
-- title:
--   At positive original ruin the exact stopped terminal retains nonnegative w(0) on creeping zero landing and vanishes on negative overshoot
-- statement:
--   For the exact original-source stopped terminal W used in the canonical P4-F theorem, suppose a strictly positive stopping time has reached ruin, the original pre-rightpayment riskProcess at that clock is nonpositive, w is zero on negative reserves, and w(0)≥0. The exact discounted terminal Term equals exp(-qτ)w(0) if the reserve lands at zero and is zero if ruin occurs by a negative overshoot; in both cases it is nonnegative. This explicitly distinguishes killed survival payoff from canonical terminal W and does not discard the creeping contribution. The nonpositive ruin reserve is an explicit source hypothesis to be discharged by the genuine path theorem.
-- source:
--   Original SpectrallyNegativeLevy, DividendStrategy riskProcess/ruinTime/rightLimit and exact P4-F terminal W; Proposition 4(i) boundary conventions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_terminal_zero_landing_vs_overshoot
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (ω : Ω) (hpos : 0 < τ ω)
    (hRuin : ruinTime X x D ω ≤ (τ ω : ℝ≥0∞))
    (hNonpos : riskProcess X x D (τ ω) ω ≤ 0) :
    (Term ω = if riskProcess X x D (τ ω) ω = 0
      then Real.exp (-(q * (τ ω : ℝ))) * w 0
      else 0) ∧ 0 ≤ Term ω := by sorry
