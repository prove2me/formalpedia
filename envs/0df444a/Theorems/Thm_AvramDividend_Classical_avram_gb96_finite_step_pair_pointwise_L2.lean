-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb96_finite_step_pair_pointwise_L2
-- name    : AvramDividend.Classical.avram_gb96_finite_step_pair_pointwise_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:06:02.144212+00:00
-- url     : https://prove2.me/theorems/abcd6b37-9b24-4d4b-a256-d80a56b04ab1
-- title:
--   Pointwise squares and covariance of bounded measurable step processes are integrable
-- statement:
--   For each fixed time, two finite sums of bounded strongly measurable random coefficients have integrable squares and cross product under a finite measure.
-- source:
--   First genuine child of gb95: finite-space integrability. Used by root-connected Gaussian gb94.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb96_finite_step_pair_pointwise_L2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (T : ℝ) (s₁ s₂ : Finset ℕ)
    (a₁ b₁ a₂ b₂ : ℕ → ℝ) (g₁ g₂ : ℕ → Ω → ℝ)
    (hg₁ : ∀ i ∈ s₁, StronglyMeasurable (g₁ i))
    (hg₂ : ∀ i ∈ s₂, StronglyMeasurable (g₂ i))
    (hB₁ : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ∈ s₁, ∀ ω, |g₁ i ω| ≤ B)
    (hB₂ : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ∈ s₂, ∀ ω, |g₂ i ω| ≤ B) :
    let K₁ : ℝ → Ω → ℝ := fun t ω =>
      s₁.sum (fun i => if a₁ i ≤ t ∧ t < b₁ i then g₁ i ω else 0)
    let K₂ : ℝ → Ω → ℝ := fun t ω =>
      s₂.sum (fun i => if a₂ i ≤ t ∧ t < b₂ i then g₂ i ω else 0)
    ∀ t : ℝ,
      Integrable (fun ω => (K₁ t ω) ^ 2) P ∧
      Integrable (fun ω => (K₂ t ω) ^ 2) P ∧
      Integrable (fun ω => K₁ t ω * K₂ t ω) P := by sorry
