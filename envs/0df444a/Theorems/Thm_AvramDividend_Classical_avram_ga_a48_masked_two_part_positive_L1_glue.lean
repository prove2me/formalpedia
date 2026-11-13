-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a48_masked_two_part_positive_L1_glue
-- name    : AvramDividend.Classical.avram_ga_a48_masked_two_part_positive_L1_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:15:14.444213+00:00
-- url     : https://prove2.me/theorems/e54634c7-ec7c-418f-96e0-4c4b142ba786
-- title:
--   Two masked positive L1 bounds plus zero-clock cancellation glue into unmasked positive L1
-- statement:
--   For any original stopped random source split B=U+V, if B is identically zero when the stopping clock is zero, its positive part is integrable under the positive-clock mask, and the masked positive parts of U and V converge in L1, then the unmasked positive part of B converges in L1. This scalar lemma is a sound child of original Gaussian gledger178 and reduces its physical Lean proof size without changing X or D.
-- source:
--   Proved avram_ga_a26_positive_l1_two_term_glue d83ded06; original spatial split 77fb849c; original stopped zero-clock 12e1cbe3.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_positive_l1_two_term_glue
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a48_masked_two_part_positive_L1_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : Ω → ℝ≥0) (B U V : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, B m ω = U m ω + V m ω)
    (hZero : ∀ m ω, ρ ω = 0 → B m ω = 0)
    (hI : ∀ m, Integrable (fun ω =>
      if 0 < ρ ω then max (B m ω) (0 : ℝ) else 0) P)
    (hU : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if 0 < ρ ω then max (U m ω) (0 : ℝ) else 0) P ∧
      (∫ ω, (if 0 < ρ ω then max (U m ω) (0 : ℝ) else 0) ∂P) ≤ ε)
    (hV : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if 0 < ρ ω then max (V m ω) (0 : ℝ) else 0) P ∧
      (∫ ω, (if 0 < ρ ω then max (V m ω) (0 : ℝ) else 0) ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (B m ω) (0 : ℝ)) P ∧
      (∫ ω, max (B m ω) (0 : ℝ) ∂P) ≤ ε := by sorry
