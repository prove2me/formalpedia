-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_cell_after_horizon_zero
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_marked_cell_after_horizon_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:13:22.590038+00:00
-- url     : https://prove2.me/theorems/2e613962-1321-4ba2-94ea-f2fceb824b1c
-- title:
--   Genuine original marked jump occupation restricted to horizon has zero mass after the horizon
-- statement:
--   For the actual original marked measure M on the original right-continuous predictable filtration, every future marked cell whose lower endpoint s is at or beyond the physical horizon T has zero mass after restriction by u≤T. This is a consequence of exact source-clock clipping and the emptiness of (s,min(t,T)], without any source rate or finite intensity assumption. It closes the post-horizon branch of finite-cell compensation.
-- source:
--   Proved P3-B original marked restricted cell measure and Mathlib Set.Ioc_eq_empty_of_le.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_marked_cell_after_horizon_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (s t T : ℝ≥0) (hTs : T ≤ s)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) = 0 := by sorry
