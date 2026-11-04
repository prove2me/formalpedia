-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_W_survival_horizon_branch
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_terminal_W_survival_horizon_branch
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:36:14.776828+00:00
-- url     : https://prove2.me/theorems/da7341b5-9ddd-4b9b-aa04-ac7f93d68a81
-- title:
--   Actual original terminal W uses postpayment reserve exactly at time zero or surviving horizon
-- statement:
--   For the source P4-F witness W and its exact source τ_n, the original post-rightpayment branch τ=0∨τ<ruin is exactly τ=0∨n<ruin. At positive ruin when the horizon reaches ruin, W remains the bookkeeping riskProcess. This lemma preserves the true zero-clock exception and full dividend-atom convention.
-- source:
--   Source exact τ embedding theorem 6b7a13a0 and canonical original W branch, no modified stochastic process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True source W chooses its postpayment branch by zero clock or survival horizon. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_terminal_W_survival_horizon_branch
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω =
      if τ ω = 0 ∨ (n : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω := by sorry
