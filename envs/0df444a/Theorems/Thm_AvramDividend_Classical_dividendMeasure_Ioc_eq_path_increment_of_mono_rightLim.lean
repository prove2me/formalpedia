-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
-- name    : AvramDividend.Classical.dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:58:14.598251+00:00
-- url     : https://prove2.me/theorems/88bfcb7c-2b00-489e-aa70-a5806d3a7041
-- title:
--   Exact Stieltjes interval mass for a monotone right-limit-fixed dividend path
-- statement:
--   If a dividend path, extended to real times by t.toNNReal, is monotone and agrees with its right limit at every real time, the associated dividendMeasure gives the Stieltjes mass of (s,t] exactly equal to ENNReal.ofReal of the difference D(t)-D(s). This generic bridge supports translated barrier and shifted running-supremum calculations.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (s t : ℝ)
    (hm : Monotone (fun r : ℝ => D r.toNNReal ω))
    (hr : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => D v.toNNReal ω) r = D r.toNNReal ω) :
    (dividendMeasure D ω) (Set.Ioc s t) =
      ENNReal.ofReal (D t.toNNReal ω - D s.toNNReal ω) := by sorry
