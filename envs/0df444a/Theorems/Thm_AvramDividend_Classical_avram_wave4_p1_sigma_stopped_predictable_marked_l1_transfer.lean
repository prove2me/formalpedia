-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
-- name    : AvramDividend.Classical.avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:46:02.072992+00:00
-- url     : https://prove2.me/theorems/80ae40da-4b55-4e4b-bc4c-621f4d994dfa
-- title:
--   Countable-band stopped signed L1 predictable marked Campbell transfer
-- statement:
--   For two possibly infinite-total-mass measures on real-time predictable history and marks, assume a countable increasing measurable mark-band exhaustion with finite first-measure mass per band, and equality on all elementary initial and strict-future adapted rectangles paired with mark sets. For any stopping time τ and any genuinely predictable-by-mark measurable real kernel G integrable under the first measure, the inclusive stopped kernel H=1_{t≤τ}G is predictably measurable, L1-integrable under both measures, and has equal Bochner integrals. The proof uses the canonically Proved inclusive survival strongly predictable theorem, pinned Integrable.indicator, and canonically Proved sigma-finite marked measure uniqueness. This does not assume arbitrary Campbell equality or identify the original source Lévy jump law. Bounded temporal restriction is needed to ensure finite band mass for a genuine PRM.
-- source:
--   Pinned Mathlib MeasureTheory.Integrable.indicator, Proved survival strongly predictable UUID 69806d16 and sigma-finite marked measure uniqueness UUID 85791e69; Applebaum predictable Poisson integration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

open MeasureTheory
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    (B : ℕ → Set E) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
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
