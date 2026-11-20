-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightshift_subclock_three_bounds
-- name    : AvramDividend.Classical.avram_f6_original_rightshift_subclock_three_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:11:25.557206+00:00
-- url     : https://prove2.me/theorems/3ead8bfb-f9d3-43c2-a1dd-71e5b6cbb4cd
-- title:
--   True original right-delayed compact stopping clock stays between input clock and its delay, below ruin clip
-- statement:
--   For the original subordinate clock sigma(k) bounded by ruin-clipped tau, the true right-delayed physical clock rho_m=min(tau,sigma(k)+1/(m+1)) lies between sigma(k) and tau and is no later than sigma(k)+1/(m+1). This deterministic sandwich preserves upper contact at ruin and supports the concrete one-sided stopped Ito/Fatou source, with no fabricated witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_rightshift_subclock_three_bounds
    {Ω : Type*} (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ (k m : ℕ) (ω : Ω),
      σ k ω ≤
        min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ∧
      min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ≤ τ ω ∧
      min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ≤
        σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)) := by sorry
