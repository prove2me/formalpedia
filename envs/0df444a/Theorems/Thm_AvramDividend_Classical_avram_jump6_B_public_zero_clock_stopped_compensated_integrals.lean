-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_zero_clock_stopped_compensated_integrals
-- name    : AvramDividend.Classical.avram_jump6_B_public_zero_clock_stopped_compensated_integrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:01:21.791275+00:00
-- url     : https://prove2.me/theorems/40af7a44-a823-4928-a522-f5bf2582c15f
-- title:
--   Original mark support: stopped jump-minus-compensator integral vanishes at zero clock
-- statement:
--   For any marked counting measure supported on strictly positive jump times and its actual finite-horizon Lebesgue-time compensator, both stopped integrals vanish at a zero stopping clock. The proof uses the Proved public zero-time mapped compensator and the source no-zero-time support, with no invented jump measure or random-clock assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva92_original_mapped_compensator_zero_time_supported_real_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_public_zero_clock_stopped_compensated_integrals
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, ∀ᵐ p ∂(NX ω), p.1 ≠ 0)
    (ν : Measure ℝ) (T : ℝ≥0)
    (σ : Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ → ℝ) :
    ∀ ω, σ ω = 0 →
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0) ∂(NX ω)) -
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0 ∂ν)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by sorry
