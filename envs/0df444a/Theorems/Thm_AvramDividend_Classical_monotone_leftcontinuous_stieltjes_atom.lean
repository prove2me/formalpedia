-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_leftcontinuous_stieltjes_atom
-- name    : AvramDividend.Classical.monotone_leftcontinuous_stieltjes_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:49:19.49225+00:00
-- url     : https://prove2.me/theorems/1eb9cd9c-7456-4860-ae6f-ff0c0c546296
-- title:
--   Stieltjes atom of a monotone left-continuous real path equals its right jump
-- statement:
--   For a monotone, left-continuous real function f, the Stieltjes measure constructed from its right-continuous modification places atomic mass ENNReal.ofReal(rightLim f(t)−f(t)) at t. Combine Mathlib's measure_singleton formula with leftLim(rightLim f)=leftLim f and leftLim f=f under left-continuity. This is exactly the probability-free lemma needed to connect the mission's dividendMeasure atoms to right-limit dividend payments.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.Stieltjes measure_singleton and Topology.Order.LeftRightLim leftLim_rightLim and ContinuousWithinAt.leftLim_eq.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.monotone_leftcontinuous_stieltjes_atom
    (f : ℝ → ℝ) (hf : Monotone f)
    (hleft : ∀ t : ℝ, ContinuousWithinAt f (Iic t) t)
    (t : ℝ) :
    hf.stieltjesFunction.measure {t} =
      ENNReal.ofReal (Function.rightLim f t - f t) := by sorry
