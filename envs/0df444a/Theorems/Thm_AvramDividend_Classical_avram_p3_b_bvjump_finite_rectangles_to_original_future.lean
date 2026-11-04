-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_finite_rectangles_to_original_future
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_finite_rectangles_to_original_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:13:33.875373+00:00
-- url     : https://prove2.me/theorems/642f7d33-e23c-4701-979f-a3191a989c05
-- title:
--   Conditional finite adapted jump rectangles extend to infinite future cylinders on the original right-continuous predictable measure space
-- statement:
--   For two measures on the original filtration's right-continuous predictable time-history/negative-mark product, agreement on all finite past-measurable (s,t] rectangles implies agreement on (s,infinity) past-measurable cylinders, assuming the finite cylinders are predictable measurable. This is a measure-continuity extension only: the original Lévy measure identification and intrinsic source-compensator rectangle identity remain upstream obligations; the statement does not assert either unconditionally. It preserves zero/infinite ENNReal mass without division.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.13); continuity of measures from below and exact Prove2Me 393b03a8 interface.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_finite_rectangles_to_original_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hCellMeas : ∀ (s t : ℝ≥0) (A : Set Ω) (B : Set ℝ),
      MeasurableSet[𝓕 s] A → MeasurableSet B →
      MeasurableSet[(@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
        ((Ioc s t ×ˢ A) ×ˢ B))
    (hRect : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        N ((Ioc s t ×ˢ A) ×ˢ B))
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    M ((Ioi s ×ˢ A) ×ˢ B) = N ((Ioi s ×ˢ A) ×ˢ B) := by sorry
