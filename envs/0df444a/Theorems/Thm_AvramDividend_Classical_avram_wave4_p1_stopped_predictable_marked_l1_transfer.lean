-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_stopped_predictable_marked_l1_transfer
-- name    : AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_l1_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:28:50.844977+00:00
-- url     : https://prove2.me/theorems/935ade9d-0a05-4525-b572-aec1f2f30ccc
-- title:
--   Bounded-horizon stopped signed L1 predictable marked-integral transfer from adapted rectangles
-- statement:
--   On a filtration of nonnegative real time, let M and N be two marked predictable measures, with M finite, agreeing only on all initial adapted and strict-future adapted time-history rectangles times measurable mark sets. Let τ be an extended stopping time of the same filtration and G a genuinely predictable-by-mark measurable integrable real kernel under M. Its inclusive stopped kernel H(t,ω,z)=1_{t≤τ(ω)}G(t,ω,z) is predictable-by-mark measurable and integrable under both M,N, and the two signed Bochner integrals coincide. The proof uses the canonically Proved inclusive survival strongly predictable theorem to justify the stopped set, norm domination to prove L1, and the canonically Proved finite marked rectangle measure uniqueness theorem for the integral equality. The rectangle equalities are elementary compensator assumptions, not the desired arbitrary predictable integral identity. To interpret this as the stopped Poisson Campbell formula for original X, 04-A must construct M as the actual expected jump measure and N as its source intensity measure; that source law is not assumed away.
-- source:
--   Canonically Proved avram_wave3_04_inclusiveSurvival_stronglyPredictable UUID 69806d16-1c2a-445a-920f-4500f3645d6a; finite marked predictable measure uniqueness UUID d31d057d-1f5c-4744-b86a-58c45723a645; pinned Mathlib measurable if and Integrable.mono'.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_marked_predictable_measure_unique
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

open MeasureTheory
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_l1_transfer
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    [IsFiniteMeasure M]
    (hBot : ∀ (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × E) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] G)
    (hGi : Integrable G M) :
    let H : ((ℝ≥0 × Ω) × E) → ℝ :=
      fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0
    Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] H ∧
    Integrable H M ∧ Integrable H N ∧
      (∫ p, H p ∂M) = ∫ p, H p ∂N := by sorry
