-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_rightJump_extended
-- name    : AvramDividend.Classical.dividendMeasure_singleton_rightJump_extended
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:59:27.783151+00:00
-- url     : https://prove2.me/theorems/8d36cde8-b4b3-4091-8439-71ef47f4344c
-- title:
--   For any dividend strategy, singleton Stieltjes mass equals the extended dividend path's right jump
-- statement:
--   For every dividend strategy and every real t, the singleton mass of dividendMeasure is exactly the positive right jump in the real-time extension s↦D(s.toNNReal). This combines the transfer of left-continuity from IsDividendStrategy with the Stieltjes atom equality under left-continuity. It is a fully unconditional measure-theoretic consequence of the dividend strategy definition and gets close to identifying the mass with rightLimit D t−D t.
-- source:
--   Children dividendStrategy_real_extension_leftContinuous and dividendMeasure_singleton_right_jump_of_leftContinuousExtension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_singleton_rightJump_extended
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ) :
    dividendMeasure D ω {t} =
      ENNReal.ofReal
        (Function.rightLim (fun s : ℝ => D s.toNNReal ω) t -
          D t.toNNReal ω) := by sorry
