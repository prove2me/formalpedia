-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_right_jump_of_leftContinuousExtension
-- name    : AvramDividend.Classical.dividendMeasure_singleton_right_jump_of_leftContinuousExtension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:56:10.69833+00:00
-- url     : https://prove2.me/theorems/bb7124af-f177-4ba7-9486-1ddf8c2a7385
-- title:
--   The dividend measure atom equals the right jump of the left-continuous extended path
-- statement:
--   Under the left-continuity of the real-time dividend path extension, its Stieltjes dividend measure singleton mass is exactly its right jump. The remaining separate task is to transfer left-continuity from IsDividendStrategy on nonnegative times to the real-time extension.
-- source:
--   Pinned Mathlib monotone Stieltjes atom lemma and the formal dividendMeasure definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_singleton_right_jump_of_leftContinuousExtension
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω)
    (hleft : ∀ t : ℝ,
      ContinuousWithinAt (fun s : ℝ => D s.toNNReal ω) (Iic t) t)
    (t : ℝ) :
    dividendMeasure D ω {t} =
      ENNReal.ofReal
        (Function.rightLim (fun s : ℝ => D s.toNNReal ω) t -
          D t.toNNReal ω) := by sorry
