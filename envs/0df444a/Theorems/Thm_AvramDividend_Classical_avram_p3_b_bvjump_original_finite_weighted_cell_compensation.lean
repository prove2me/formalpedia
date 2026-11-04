-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_weighted_cell_compensation
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_finite_weighted_cell_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:28:23.83032+00:00
-- url     : https://prove2.me/theorems/65d871a8-45b5-42db-8806-8da37befdd0e
-- title:
--   Original predictable finite simple marked cells compensate in ENNReal without finite-activity assumptions
-- statement:
--   On exactly the original right-continuous predictable marked measurable space, assume equality M=N of finite-cell masses supplied by the original source compensator. Every finite nonnegative predictable simple marked-cell sum has identical mass under M and N, with no finite-total-intensity requirement. ENNReal multiplication and summation preserve the 0·∞=0 edge case. Explicitly conditional on source finite-cell rectangle compensation; does not assume a new Poisson model or mark compensator for the original process.
-- source:
--   Mathlib Finset.sum_congr; prior P3-B original marked finite-cell helpers; Avram Proposition 4(i).

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_finite_weighted_cell_compensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (A : ℕ → Set Ω) (B : ℕ → Set ℝ)
    (c : ℕ → ℝ≥0∞)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (hB : ∀ i ∈ S, MeasurableSet (B i)) :
    (∑ i ∈ S, c i * M ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i)) =
      (∑ i ∈ S, c i * N ((Ioc (s i) (t i) ×ˢ A i) ×ˢ B i)) := by sorry
