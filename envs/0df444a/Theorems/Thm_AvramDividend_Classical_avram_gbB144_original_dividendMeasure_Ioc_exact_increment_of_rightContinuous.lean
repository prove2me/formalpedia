-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB144_original_dividendMeasure_Ioc_exact_increment_of_rightContinuous
-- name    : AvramDividend.Classical.avram_gbB144_original_dividendMeasure_Ioc_exact_increment_of_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:59:42.218932+00:00
-- url     : https://prove2.me/theorems/d1f2c698-dc78-48bb-a64a-a74b16b2b6ad
-- title:
--   Exact original dividend Stieltjes measure of a physical Ioc cell equals regulator increment
-- statement:
--   For any original cumulative dividend strategy whose real-time NNReal-coerced path is monotone and right-continuous at two endpoints, the original dividendMeasure assigns their physical interval Ioc(a,b) exactly the ENNReal of the regulator increment D(b)-D(a). This bridges the actual source Stieltjes measure to discrete cash cells, without replacing the original measure with an abstract surrogate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB144_original_dividendMeasure_Ioc_exact_increment_of_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (a b : ℝ)
    (hMono : Monotone (fun t : ℝ => D t.toNNReal ω))
    (hContA : ContinuousWithinAt
      (fun t : ℝ => D t.toNNReal ω) (Ici a) a)
    (hContB : ContinuousWithinAt
      (fun t : ℝ => D t.toNNReal ω) (Ici b) b) :
    dividendMeasure D ω (Ioc a b) =
      ENNReal.ofReal
        (D b.toNNReal ω - D a.toNNReal ω) := by sorry
