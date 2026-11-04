-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_ruin_zero_landing_terminal_w0
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_zero_landing_terminal_w0
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:11:06.322362+00:00
-- url     : https://prove2.me/theorems/ab19e5d6-7c21-4295-b651-748bf9761005
-- title:
--   Actual positive ruin landing at zero retains discounted w(0) rather than overshoot zero
-- statement:
--   At positive original exact ruin time, the hW branch is the source riskProcess, not the post-rightpayment reserve. If that ruin reserve is exactly zero, the true discounted terminal is exp(-qτ)w(0). This prevents treating zero landing as a negative overshoot, and does not strengthen source w(0)≥0 to equality.
-- source:
--   Exact original P4-F stopped W and Term conventions 0dda1be7-9d8b-41e0-ae51-55fab5c38e22.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At positive original ruin landing exactly on zero, the discounted terminal retains w(0). -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_positive_ruin_zero_landing_terminal_w0
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ξ, W ξ =
      if τ ξ = 0 ∨ (τ ξ : ℝ≥0∞) < ruinTime X x D ξ
      then x + X.X (τ ξ) ξ - rightLimit D (τ ξ) ξ
      else riskProcess X x D (τ ξ) ξ)
    (w : ℝ → ℝ)
    (hTerm : ∀ ξ, Term ξ =
      Real.exp (-(q * (τ ξ : ℝ))) * w (W ξ))
    (ω : Ω) (hτpos : 0 < τ ω)
    (hτruin : (τ ω : ℝ≥0∞) = ruinTime X x D ω)
    (hLandZero : riskProcess X x D (τ ω) ω = 0) :
    Term ω = Real.exp (-(q * (τ ω : ℝ))) * w 0 := by sorry
