-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb97_finite_step_pair_time_energy_L1
-- name    : AvramDividend.Classical.avram_gb97_finite_step_pair_time_energy_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:06:02.631031+00:00
-- url     : https://prove2.me/theorems/43dfb3b3-552d-4d06-96a4-a4c8aa405ab6
-- title:
--   Time energy of bounded measurable finite-step processes is integrable
-- statement:
--   The expected squares and cross product of two bounded measurable finite-step processes are finite linear combinations of time-interval indicators, hence integrable over a finite time horizon.
-- source:
--   Second genuine child of gb95: finite-horizon measurability and integrability. Uses original measure coefficients with no auxiliary process.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb97_finite_step_pair_time_energy_L1
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
      Integrable (fun ω => K₁ t ω * K₂ t ω) P) →
    IntegrableOn (fun t => ∫ ω, (K₁ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, (K₂ t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume ∧
    IntegrableOn (fun t => ∫ ω, K₁ t ω * K₂ t ω ∂P)
      (Ioo (0 : ℝ) T) volume := by sorry
