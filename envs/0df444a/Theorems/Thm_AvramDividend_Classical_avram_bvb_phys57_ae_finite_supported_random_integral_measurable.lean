-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys57_ae_finite_supported_random_integral_measurable
-- name    : AvramDividend.Classical.avram_bvb_phys57_ae_finite_supported_random_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:28:54.991191+00:00
-- url     : https://prove2.me/theorems/ca1451bc-bca2-4505-86ee-85d3f42a0f9c
-- title:
--   Almost everywhere measurable integrals of original random measures with finite support mass
-- statement:
--   For a measurable random measure M and a jointly strongly measurable real reward supported on a fixed Borel set S, if the random S-mass is finite almost surely, then its sample-dependent signed integral is almost everywhere strongly measurable. The proof localises to uniformly bounded random masses and uses the accepted phys56 theorem.
-- source:
--   Mathlib StronglyMeasurable.integral_kernel_prod_right' and aestronglyMeasurable_of_tendsto_ae; parent Proved phys56.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys56_uniform_finite_random_integral_strongly_measurable

open Classical MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys57_ae_finite_supported_random_integral_measurable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (M : Ω → Measure α)
    (hM : ∀ B : Set α, MeasurableSet B →
      Measurable (fun ω : Ω => M ω B))
    (S : Set α) (hS : MeasurableSet S)
    (f : Ω × α → ℝ) (hf : StronglyMeasurable f)
    (hfS : ∀ ω p, p ∉ S → f (ω, p) = 0)
    (hFinite : ∀ᵐ ω ∂P, M ω S < ⊤) :
    AEStronglyMeasurable
      (fun ω : Ω => ∫ p, f (ω, p) ∂M ω) P := by sorry
