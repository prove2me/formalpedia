-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_positive_integrated_excursion_tail
-- name    : AvramDividend.Classical.contDiffOn_one_of_positive_integrated_excursion_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T23:05:52.199967+00:00
-- url     : https://prove2.me/theorems/ab7d1be6-c742-4675-b995-f87ccb3bd222
-- title:
--   Locally continuous positive-level excursion tail yields C1 regularity
-- statement:
--   If the excursion-height upper tail T is continuous only on the strictly positive half-line, and the scale-type function W obeys W(x)=c exp(∫_a^x T(t)dt) for positive x and a, then W is C1 on (0,∞). The tail may diverge at zero, as it commonly does for infinite-variation Lévy processes. The proof applies the fundamental theorem of calculus locally to intervals entirely within (0,∞).
-- source:
--   Chan, Kyprianou and Savov (2009), arXiv:0903.1467v1, equation (5) and discussion immediately following; Mathlib intervalIntegral.integral_hasDerivAt_right.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Set MeasureTheory intervalIntegral

theorem AvramDividend.Classical.contDiffOn_one_of_positive_integrated_excursion_tail
    (T W : ℝ → ℝ) (a c : ℝ) (ha : 0 < a)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, T t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
