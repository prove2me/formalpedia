-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_W_exact_horizon_branch
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_terminal_W_exact_horizon_branch
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:01:37.7832+00:00
-- url     : https://prove2.me/theorems/f6147667-c676-4466-bbf4-14c5254bf9a1
-- title:
--   Literal original P4-F W branch equals zero-clock or strictly surviving finite horizon
-- statement:
--   At τ=(min(ruinTime,n)).toNNReal, the exact P4-F W expression simplifies to postpayment state when τ=0 or deterministic horizon n strictly precedes ruin, and prepayment riskProcess otherwise. This retains special time-zero behavior and assigns equality ruin=n to the ruin side; it uses the already Proved exact original clipped-clock NNReal bounds without changing W or any payout atom.
-- source:
--   Exact original P4-F hW and Proved avram_wave7_08_source_truncated_clock_nnreal_bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True source W chooses its postpayment branch by zero clock or survival horizon. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_terminal_W_exact_horizon_branch
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
