-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_original_stopped_L1_limit_zero_mean_zero_clock
-- name    : AvramDividend.Classical.avram_jump6_B_public_original_stopped_L1_limit_zero_mean_zero_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:12:27.990184+00:00
-- url     : https://prove2.me/theorems/36a09e2a-f6cb-47d0-81fc-cabe0a8ac2f7
-- title:
--   Source-exact stopped L1 compensated martingale limit preserves zero mean and zero stopping-clock value
-- statement:
--   For the same original physical stopped process, a sequence of integrable zero-mean compensated stochastic source terms whose actual stopped values vanish at a zero clock, with genuine L1 and almost sure convergence, yields an integrable limit with exactly zero expected value and zero-clock value almost surely. This uses the public restricted L1 convergence theorem and pathwise uniqueness of limits, with no invented source witness or axiom.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine L1 convergence and almost-everywhere limits inherit centred and zero-clock properties. -/

theorem AvramDividend.Classical.avram_jump6_B_public_original_stopped_L1_limit_zero_mean_zero_clock
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
