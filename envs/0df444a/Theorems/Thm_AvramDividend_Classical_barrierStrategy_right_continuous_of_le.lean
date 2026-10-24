-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
-- name    : AvramDividend.Classical.barrierStrategy_right_continuous_of_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:00:39.512508+00:00
-- url     : https://prove2.me/theorems/74159b66-6b55-491a-ba83-91d1dd1c0618
-- title:
--   Barrier strategy right continuity for every initial reserve at or below its barrier
-- statement:
--   If the initial reserve x does not exceed the barrier a, the barrier dividend strategy has right-continuous sample paths for all real x and a, without any nonnegativity assumptions on either. Deduce this from the right-continuity of the strategy initially at the barrier, the pointwise offset identity, and continuity of subtraction and maximum.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_offset_of_le

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_right_continuous_of_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X x a s ω) (Ici t) t := by sorry
