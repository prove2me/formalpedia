-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_leftcontinuous_stieltjes_measure_Ico
-- name    : AvramDividend.Classical.monotone_leftcontinuous_stieltjes_measure_Ico
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:13:14.334743+00:00
-- url     : https://prove2.me/theorems/602ae8fe-b648-42e4-bbb8-127812ac8a74
-- title:
--   The Stieltjes measure of a monotone left-continuous path on [a,b) equals its total increment
-- statement:
--   For any monotone left-continuous real path f, the Stieltjes measure of its right-continuous modification assigns to the half-open interval [a,b) the exact increment ENNReal.ofReal(f(b)−f(a)). Mathlib gives the Stieltjes Ico mass as ofReal(leftLim(g,b)−leftLim(g,a)) for g=rightLim f; monotonicity and left-continuity identify these left limits with f. This is the crucial interval-mass identity covering both continuous dividend increments and jumps of a dividend strategy.
-- source:
--   Pinned Mathlib StieltjesFunction.measure_Ico; leftLim_rightLim, Monotone.tendsto_leftLim and ContinuousWithinAt.leftLim_eq.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.monotone_leftcontinuous_stieltjes_measure_Ico
    (f : ℝ → ℝ) (hf : Monotone f)
    (hleft : ∀ t : ℝ, ContinuousWithinAt f (Iic t) t)
    (a b : ℝ) :
    hf.stieltjesFunction.measure (Ico a b) =
      ENNReal.ofReal (f b - f a) := by sorry
