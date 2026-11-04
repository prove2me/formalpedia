-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_infinite_ruin_stopped_horizon_postpayment_terminal
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_infinite_ruin_stopped_horizon_postpayment_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:55:58.376265+00:00
-- url     : https://prove2.me/theorems/bc0c27ed-00c6-4d0a-b5e9-bdeca056a868
-- title:
--   Original infinite ruin selects finite stopped horizon and rightpayment terminal reserve
-- statement:
--   At infinite original ruin time, the exact source min(ruin,n) stopped clock equals finite n and the original terminal W selects the surviving post-rightpayment capital at n, including the case n=0. No almost-sure finiteness of ruin is assumed, and the source branch choice is preserved.
-- source:
--   Exact stopped clock and original piecewise W binders of P4-F 0dda1be7-9d8b-41e0-ae51-55fab5c38e22.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Infinite original ruin preserves the rightpayment terminal at the fixed horizon. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_infinite_ruin_stopped_horizon_postpayment_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ruinTime X x D ω = ⊤ →
      τ ω = (n : ℝ≥0) ∧
      W ω = x + X.X (n : ℝ≥0) ω - rightLimit D (n : ℝ≥0) ω := by sorry
