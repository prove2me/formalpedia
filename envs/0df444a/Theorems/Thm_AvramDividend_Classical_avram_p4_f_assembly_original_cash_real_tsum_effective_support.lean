-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_real_tsum_effective_support
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_tsum_effective_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:18:38.85589+00:00
-- url     : https://prove2.me/theorems/efed7f7e-8ed8-41ca-bbe3-fcec2297774a
-- title:
--   Exact original discounted Stieltjes Cash atom sum restricts to its genuine nonzero singleton support
-- statement:
--   A source real-indexed atomic dividend measure may include times of zero singleton mass. The full discounted real Cash atomic sum equals the sum over just its effective nonzero singleton support, preserving the source real indices and the true ENNReal discounted mass. This is the needed zero-atom filtering step before applying genuine clock certificates to all surviving indices.
-- source:
--   Source original discounted Cash atomic measure 188366d0 and pinned Mathlib tsum_subtype_eq_of_support_subset. No additional stochastic hypotheses.

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_cash_real_tsum_effective_support
    (A : Set ℝ) (μatom : Measure ℝ) (q : ℝ) :
    (∑' a : A,
      (ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}).toReal) =
    ∑' a : {a : A // μatom {a.1} ≠ 0},
      (ENNReal.ofReal (Real.exp (-(q * a.1.1))) *
        μatom {a.1.1}).toReal := by sorry
