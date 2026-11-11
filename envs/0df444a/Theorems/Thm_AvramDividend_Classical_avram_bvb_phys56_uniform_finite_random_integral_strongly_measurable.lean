-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys56_uniform_finite_random_integral_strongly_measurable
-- name    : AvramDividend.Classical.avram_bvb_phys56_uniform_finite_random_integral_strongly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:15:48.119404+00:00
-- url     : https://prove2.me/theorems/1da54ad0-2cde-4032-a24d-0a4be6a5c3b5
-- title:
--   Strong measurability of a random integral under uniformly bounded measure masses
-- statement:
--   For an original random measure whose evaluation on each measurable set is measurable, a global finite bound on its total mass ensures the integral of every jointly strongly measurable signed reward is strongly measurable in the sample parameter. This will supply the finite-count localisation step for Avram phys49.
-- source:
--   Mathlib.Probability.Kernel.MeasurableIntegral, StronglyMeasurable.integral_kernel_prod_right'.

import Mathlib

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys56_uniform_finite_random_integral_strongly_measurable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (M : Ω → Measure α)
    (hM : ∀ S : Set α, MeasurableSet S →
      Measurable (fun ω : Ω => M ω S))
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hMass : ∀ ω : Ω, M ω Set.univ ≤ C)
    (f : Ω × α → ℝ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun ω : Ω => ∫ p, f (ω, p) ∂M ω) := by sorry
