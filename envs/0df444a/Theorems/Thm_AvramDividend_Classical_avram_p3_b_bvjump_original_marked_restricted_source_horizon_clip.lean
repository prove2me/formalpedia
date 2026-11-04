-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_source_horizon_clip
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_marked_restricted_source_horizon_clip
-- status  : Open
-- author  : @WillR
-- created : 2026-11-03T10:46:48.215681+00:00
-- url     : https://prove2.me/theorems/ec71350c-79c0-4225-9177-a22922aa8fc7
-- title:
--   Genuine original marked source occupation clipped at stopping horizon is unchanged by clipping source interval
-- statement:
--   On the genuine original right-continuous predictable marked-jump occupation measure M, restricting at the true finite stopping horizon T makes any adapted marked rectangle (s,t]×A×B equal in mass to its clipped version (s,min(t,T)]×A×B. This is purely the already accepted source marked-cell measure restriction identity, with no Lévy rate, finite first moment, or surrogate process.
-- source:
--   Proved P3-B original marked restricted cell measure and min-order identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_marked_restricted_source_horizon_clip
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (s t T : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
      (M.restrict {p | p.1.1 ≤ T})
        ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by sorry
