-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb102_finite_step_joint_stronglyMeasurable
-- name    : AvramDividend.Classical.avram_gb102_finite_step_joint_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:22:46.569484+00:00
-- url     : https://prove2.me/theorems/8336ad82-06c5-4f7d-a667-5247dfff69e0
-- title:
--   Finite deterministic step process is jointly strongly measurable in time and outcome
-- statement:
--   A finite sum of time-interval-indicator masks times strongly measurable outcome coefficients is jointly strongly measurable in the time/outcome product space.
-- source:
--   Finite-step time-measurability child needed for the original Gaussian gb97.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gb102_finite_step_joint_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ℕ) (a b : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (hg : ∀ i ∈ s, StronglyMeasurable (g i)) :
    StronglyMeasurable (fun z : ℝ × Ω =>
      s.sum (fun i =>
        if a i ≤ z.1 ∧ z.1 < b i then g i z.2 else 0)) := by sorry
