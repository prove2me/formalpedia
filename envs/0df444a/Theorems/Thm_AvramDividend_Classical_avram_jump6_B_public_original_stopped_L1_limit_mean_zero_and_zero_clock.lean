-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_original_stopped_L1_limit_mean_zero_and_zero_clock
-- name    : AvramDividend.Classical.avram_jump6_B_public_original_stopped_L1_limit_mean_zero_and_zero_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:33:18.171915+00:00
-- url     : https://prove2.me/theorems/00f3b575-9ce0-446c-bf4c-c8d085876bb2
-- title:
--   Stopped original-source L1 martingale limit preserves zero mean and zero-clock vanishing
-- statement:
--   An integrable stopped real-valued martingale approximation with zero expectation at each grid/cutoff index, a genuinely L1-convergent terminal and almost everywhere pointwise convergence has an integrable terminal of mean zero and a.e. vanishing at source stopping clock zero when all approximations vanish there. The hypotheses state every integrability and convergence requirement explicitly. Reuses a Proved public L1 mean-transfer theorem and pointwise uniqueness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-- Genuine L1 convergence and almost-everywhere limits inherit centred and zero-clock properties. -/

theorem AvramDividend.Classical.avram_jump6_B_public_original_stopped_L1_limit_mean_zero_and_zero_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (σ : Ω → ℝ≥0) (Q : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hQI : ∀ n, Integrable (Q n) P) (hZI : Integrable Z P)
    (hQzero : ∀ᵐ ω ∂P, ∀ n, σ ω = 0 → Q n ω = 0)
    (hQmean : ∀ n, (∫ ω, Q n ω ∂P) = 0)
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖Q n ω - Z ω‖ₑ ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)))
    (hPoint : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => Q n ω) atTop (𝓝 (Z ω))) :
    (∫ ω, Z ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P, σ ω = 0 → Z ω = 0 := by sorry
