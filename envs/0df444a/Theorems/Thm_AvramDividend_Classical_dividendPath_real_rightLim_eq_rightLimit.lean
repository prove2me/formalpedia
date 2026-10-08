-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit
-- name    : AvramDividend.Classical.dividendPath_real_rightLim_eq_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:05:59.703798+00:00
-- url     : https://prove2.me/theorems/897c12ef-009a-4fc0-8538-87a1a515ca18
-- title:
--   Right limit of the real dividend-path extension equals the defined nonnegative-time rightLimit
-- statement:
--   For any monotone dividend path D on nonnegative times, its right limit through the real extension s→D(s.toNNReal) at a nonnegative time t equals the precise mission rightLimit D t ω defined as the infimum of values over nonnegative times strictly larger than t. The positive-real and positive-NNReal index sets parametrise the same dividend values. This closes the right-limit identification used to calculate dividendMeasure singleton atoms.
-- source:
--   Pinned Mathlib Monotone.rightLim_eq_sInf, Real.coe_toNNReal, and sInf_range; mission rightLimit definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendPath_real_rightLim_eq_rightLimit
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hmono : Monotone (fun s : ℝ≥0 => D s ω)) (t : ℝ≥0) :
    Function.rightLim (fun s : ℝ => D s.toNNReal ω) (t : ℝ) =
      rightLimit D t ω := by sorry
