-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a25_positive_l1_glue
-- name    : AvramDividend.Classical.avram_ga_a25_positive_l1_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:55:29.530202+00:00
-- url     : https://prove2.me/theorems/df4b2d03-4c93-46dd-acfe-c2dcb2393daa
-- title:
--   One-sided L1 gluing of absolute and positive-part errors
-- statement:
--   Given a pointwise residual split into an absolute-L1-small error and a positive-part-L1-small error, plus positive residual integrability, deduce that the positive-part residual converges in L1. This is an independent generic measure-theory lemma for the genuine Gaussian source route.
-- source:
--   Pointwise max(A+B,0) at most abs(A)+max(B,0), followed by integral monotonicity and half-epsilon argument. This is for the gledger50 to gledger178 alternative.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_a25_positive_l1_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S M G A B : ℕ → Ω → ℝ)
    (hAB : ∀ m ω, S m ω - M m ω - G m ω = A m ω + B m ω)
    (hI : ∀ m, Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |A m ω|) P ∧ (∫ ω, |A m ω| ∂P) ≤ ε)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (B m ω) 0) P ∧
      (∫ ω, max (B m ω) 0 ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P ∧
      (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) ≤ ε := by sorry
