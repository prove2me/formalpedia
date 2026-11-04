-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_marked_restricted_cell_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:51:47.964211+00:00
-- url     : https://prove2.me/theorems/5ebbb833-c455-499d-bab5-c4cbe78b479a
-- title:
--   Original stopped predictable source rectangle restriction exactly equals its horizon-clipped measure
-- statement:
--   On the same original right-continuous predictable filtration and original marked measure M, restricting by the genuine source clock {u≤T} and evaluating a finite adapted (s,t]×A×B rectangle equals evaluating (s,min(t,T)]×A×B against M. The real original measurable cell is handled explicitly; no Poisson model, compensator identity, stopping theorem or intensity assumption is needed. This is used to lift P2's source rate through the true finite physical horizon without breaking 0·∞ cases.
-- source:
--   Mathlib Measure.restrict_apply; already Proved P3-B predictable finite cell and physical source horizon clipping.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_finite_cell_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_cell_horizon_clip
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_marked_restricted_cell_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (s t T : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
    M ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by sorry
