-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_gaussian_two_absolute_errors_glue_measurable
-- name    : AvramDividend.Classical.avram_a20_gaussian_two_absolute_errors_glue_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:30:51.830316+00:00
-- url     : https://prove2.me/theorems/dc7d6b9f-fa6e-47a0-9fad-2ca43e91ca61
-- title:
--   Corrected original Gaussian two-error positive L1 gluing with explicitly measurable residual
-- statement:
--   The original gledger141 positive-part gluing needs a measurability premise: vanishing absolute-value L1 controls alone do not establish measurability of a signed residual. For a truly a.e. strongly measurable same-source residual that splits pointwise into two errors with vanishing L1 norms, its positive part is integrable and its integral tends to zero. This repairs the missing premise while retaining the original stochastic Gaussian residual interpretation.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a20_gaussian_two_absolute_errors_glue_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S M G A B : ℕ → Ω → ℝ)
    (hAB : ∀ m ω, S m ω - M m ω - G m ω = A m ω + B m ω)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => S m ω - M m ω - G m ω) P)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |A m ω|) P ∧
      (∫ ω, |A m ω| ∂P) ≤ ε)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |B m ω|) P ∧
      (∫ ω, |B m ω| ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P ∧
      (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) ≤ ε := by sorry
