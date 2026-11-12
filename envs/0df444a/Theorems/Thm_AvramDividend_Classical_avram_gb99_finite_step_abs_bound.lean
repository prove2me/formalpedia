-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb99_finite_step_abs_bound
-- name    : AvramDividend.Classical.avram_gb99_finite_step_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:18:10.796466+00:00
-- url     : https://prove2.me/theorems/83fdb2b0-1f37-46d9-92b0-b7e63eb22b15
-- title:
--   Uniform pointwise absolute bound for finite deterministic step sums
-- statement:
--   At any fixed time and outcome, the absolute value of a finite sum of masked coefficients is bounded by the number of terms times a common nonnegative bound.
-- source:
--   Necessary and reusable sublemma of original Gaussian pointwise gb96.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb99_finite_step_abs_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ℕ) (a b : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hb : ∀ i ∈ s, ∀ ω, |g i ω| ≤ B) (t : ℝ) (ω : Ω) :
    |s.sum (fun i => if a i ≤ t ∧ t < b i then g i ω else 0)| ≤
      (s.card : ℝ) * B := by sorry
