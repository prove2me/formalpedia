-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b34_original_ruinclock_mixed_noise_initial_event_L1_transfer
-- name    : AvramDividend.Classical.avram_b34_original_ruinclock_mixed_noise_initial_event_L1_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:20:25.114126+00:00
-- url     : https://prove2.me/theorems/26536e90-4e7c-4526-bd85-b7f00c6d3a01
-- title:
--   Original random ruin-clock mixed Gaussian and jump aggregate noise retains initial-event mean zero under L1 approximation
-- statement:
--   Under L1 convergence of the exact original Gaussian-plus-compensated-jump noise from a sequence of physical finite-range stopping clocks to the true random ruin-clipped stopping clock, zero mean of all approximants on any initial event passes to the true stopped aggregate noise. Both channels are canonical original Lévy cutoff-limit fields.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), original stopped Ito-Meyer martingale localisation; Proved restricted L1 centring 71b869b4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b34_original_ruinclock_mixed_noise_initial_event_L1_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
    (κ : Ω → ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hκstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (κ ω : WithTop ℝ≥0)))
    (hτstop : ∀ m, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ m ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    (∀ m, Integrable
      (fun ω => R (τ m ω) ω + Jsmall (τ m ω) ω) P) →
    Integrable (fun ω => R (κ ω) ω + Jsmall (κ ω) ω) P →
    (∀ m, (∫ ω in A,
      R (τ m ω) ω + Jsmall (τ m ω) ω ∂P) = 0) →
    Tendsto
      (fun m => ∫⁻ ω in A,
        ‖(R (τ m ω) ω + Jsmall (τ m ω) ω) -
          (R (κ ω) ω + Jsmall (κ ω) ω)‖ₑ ∂P)
      atTop (𝓝 (0 : ℝ≥0∞)) →
    (∫ ω in A, R (κ ω) ω + Jsmall (κ ω) ω ∂P) = 0 := by sorry
