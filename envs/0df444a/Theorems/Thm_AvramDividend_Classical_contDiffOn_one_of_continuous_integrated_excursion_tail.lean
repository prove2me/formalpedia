-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_continuous_integrated_excursion_tail
-- name    : AvramDividend.Classical.contDiffOn_one_of_continuous_integrated_excursion_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T23:03:48.831317+00:00
-- url     : https://prove2.me/theorems/8c27b581-50fb-4c28-b574-2640878ab9fa
-- title:
--   Continuous integrated excursion tail yields C1 scale-function regularity
-- statement:
--   Let a continuous real tail function T control a positive-level function W through the integrated identity W(x)=c exp(∫_a^x T(t)dt). Then W is continuously differentiable on (0,∞). This deterministic fundamental-theorem-of-calculus bridge converts the standard excursion-height integral representation of scale functions into C1 regularity without any stochastic standing or moment assumptions.
-- source:
--   Chan, Kyprianou and Savov (2009), arXiv:0903.1467v1, equation (5) and its derivative; Mathlib Continuous.deriv_integral and contDiff_one_iff_deriv.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Set MeasureTheory intervalIntegral

theorem AvramDividend.Classical.contDiffOn_one_of_continuous_integrated_excursion_tail
    (T W : ℝ → ℝ) (a c : ℝ)
    (hT : Continuous T)
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, T t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
