-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a46_positive_negative_L1_to_absolute
-- name    : AvramDividend.Classical.avram_ga_a46_positive_negative_L1_to_absolute
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:13:24.521209+00:00
-- url     : https://prove2.me/theorems/034cc31a-c396-4d7c-ac18-5292b6161055
-- title:
--   Positive and negative L1 tails combine into an absolute L1 tail
-- statement:
--   If the positive and negative parts of each real-valued stochastic error have integrable eventual expectations bounded by every epsilon, then its absolute value is eventually integrable with expectation at most epsilon. The proof is the exact identity |r| = max(r,0)+max(-r,0), and a common cutoff chosen using epsilon/2.
-- source:
--   Generic bridge for original stopped Gaussian Taylor absolute L1 c47f646c, based on positive gledger178 and a new negative physical child.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_a46_positive_negative_L1_to_absolute
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ)
    (hPos : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (f m ω) (0 : ℝ)) P ∧
      (∫ ω, max (f m ω) (0 : ℝ) ∂P) ≤ ε)
    (hNeg : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (-f m ω) (0 : ℝ)) P ∧
      (∫ ω, max (-f m ω) (0 : ℝ) ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |f m ω|) P ∧
      (∫ ω, |f m ω| ∂P) ≤ ε := by sorry
