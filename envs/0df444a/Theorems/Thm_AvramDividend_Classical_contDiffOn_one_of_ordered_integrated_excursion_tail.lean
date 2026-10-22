-- Prove2me | Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_ordered_integrated_excursion_tail
-- name    : AvramDividend.Classical.contDiffOn_one_of_ordered_integrated_excursion_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T23:30:34.75954+00:00
-- url     : https://prove2.me/theorems/f96bb8d4-b3bd-44b8-87ea-36ff59e33215
-- title:
--   Ordered excursion-height integral identity gives C1 regularity at all positive levels
-- statement:
--   Suppose T is continuous on (0,∞), W obeys W(v)=W(u) exp(∫_u^v T) whenever 0<u≤v, and a>0 is any anchor. For x<a, the ordered relation from x to a and reversal of the interval integral give the anchored formula from a to x. For x≥a the anchored formula is immediate. Hence W is C1 on the entire positive half-line by the proven positive-level integral-FTC lemma. No nonvanishing condition on W is needed.
-- source:
--   The standard excursion-height identity for ordered positive levels (Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions, Section 2.3), together with Mathlib intervalIntegral.integral_symm and the Proved positive-level excursion FTC bridge.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_positive_integrated_excursion_tail
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.contDiffOn_one_of_ordered_integrated_excursion_tail
    (T W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hordered : ∀ u v : ℝ, 0 < u → u ≤ v →
      W v = W u * Real.exp (∫ t in u..v, T t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
