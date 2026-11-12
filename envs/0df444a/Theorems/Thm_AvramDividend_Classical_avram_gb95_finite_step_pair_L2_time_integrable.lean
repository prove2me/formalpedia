-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb95_finite_step_pair_L2_time_integrable
-- name    : AvramDividend.Classical.avram_gb95_finite_step_pair_L2_time_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:59:06.554602+00:00
-- url     : https://prove2.me/theorems/c9d0e587-cebc-48e4-bb79-e3bb482c1c9f
-- title:
--   Bounded measurable finite-step coefficient pairs have square-integrable space-time rewards
-- statement:
--   A pair of finite deterministic time-step processes with bounded, strongly measurable random coefficients has integrable squares and products on each probability fibre, and their expected squares and product are integrable over any bounded time horizon.
-- source:
--   Sound analytic reduction for original-process Gaussian time-energy theorem gb94. Does not assume independence of a surrogate Brownian process.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb95_finite_step_pair_L2_time_integrable
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
    (∀ t : ℝ,
      Integrable (fun ω => (K₁ t ω) ^ 2) P ∧
      Integrable (fun ω => (K₂ t ω) ^ 2) P ∧
      Integrable (fun ω => K₁ t ω * K₂ t ω) P) ∧
    IntegrableOn (fun t => ∫ ω, (K₁ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, (K₂ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, K₁ t ω * K₂ t ω ∂P)
      (Ioo (0 : ℝ) T) volume := by sorry
