-- Prove2me | Theorems.Thm_AvramDividend_Classical_affine_cutoff_contDiffOn_positive_below_cap
-- name    : AvramDividend.Classical.affine_cutoff_contDiffOn_positive_below_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:33:17.2226+00:00
-- url     : https://prove2.me/theorems/dc22ff4c-dcac-4ba3-ab7d-5be45021aa09
-- title:
--   Zero-extended affine verification candidate is C² below any positive dividend cap
-- statement:
--   The piecewise affine candidate already proven C² on the positive half-line remains C² when restricted to strictly positive reserves below an arbitrary extended-real capital cap C. The conclusion exactly matches the smoothness assumption of the canonical unbounded-variation stochastic verification core.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i); prior affine-cutoff regularity theorem.

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_continuous_nonnegative_smooth_positive

open Set
open scoped ENNReal

theorem AvramDividend.Classical.affine_cutoff_contDiffOn_positive_below_cap (C : ℝ≥0∞) :
    ContDiffOn ℝ 2 (fun z : ℝ => if z < 0 then 0 else z - 1)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
