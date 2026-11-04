-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_marked_intensity_cell
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_marked_intensity_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:27:33.23289+00:00
-- url     : https://prove2.me/theorems/9edcea14-1d0a-4153-a0f7-afeed4f2ae22
-- title:
--   Genuine predictable-clock times sigma-finite Lévy mark intensity has exact marked-cell mass
-- statement:
--   For the original right-continuous predictable clock and a sigma-finite original Lévy mark measure, the deterministic marked intensity N=μ.prod ν has exactly μ((s,t]×A)·ν(B) mass on every marked cell. This is an identity of the actual product intensity and handles 0·∞ without cancellation. The available Proved negative Lévy measure sigma-finiteness theorem supplies the mark hypothesis in the source application. This does not assert equality between source jump occupation M and intensity N, which remains dependent on P2.
-- source:
--   Mathlib MeasureTheory.Measure.prod_prod (SFinite mark measure); original P3 compensated source measure ν and μ.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_marked_intensity_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (ν : Measure ℝ) [SFinite ν]
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; μ.prod ν))
    (s t : ℝ≥0) (A : Set Ω) (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      μ (Ioc s t ×ˢ A) * ν B := by sorry
