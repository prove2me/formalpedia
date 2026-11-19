-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_public_stopped_compensation_zero_clock
-- name    : AvramDividend.Classical.avram_pj_workerC_public_stopped_compensation_zero_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:38:33.724961+00:00
-- url     : https://prove2.me/theorems/d83eceec-192a-4f6d-8e79-2ff8aca7f46d
-- title:
--   Public source-supported zero-clock stopped negative-jump compensation cancellation
-- statement:
--   For an actual negative-mark counting measure supported only at strictly positive times, the stopped sample-path jump integral and real-time Lévy compensator are both exactly zero at a zero stopping clock. This is the reusable generic, public, measure-theoretic zero-clock cancellation with no independence assumptions.
-- source:
--   Public Proved efd7b440 mapped compensator has zero time-zero integral; original mapped NX positive-time support. Direct ae integral congruence proves the jump source vanishes.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_public_stopped_compensation_zero_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, ∀ᵐ p ∂(NX ω), p.1 ≠ 0)
    (ν : Measure ℝ) (T : ℝ≥0)
    (σ : Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ → ℝ) :
    ∀ ω, σ ω = 0 →
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0) ∂(NX ω)) -
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0 ∂ν)
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by sorry
