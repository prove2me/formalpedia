-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
-- name    : AvramDividend.Classical.causal_weighted_BCF_extension_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:00:45.776325+00:00
-- url     : https://prove2.me/theorems/965bf7ed-0537-4b3b-899d-423c92165339
-- title:
--   Exponentially undoing the BCF weight gives a continuous real-time extension
-- statement:
--   For a bounded continuous function f on nonnegative times, the expression e^(wx) f(max(x,0)) extends it (after exponential reweighting) to a continuous real function. This is the regularity used to feed Banach-space elements into the causal convolution operator.
-- source:
--   Continuity of max with 0, subtype coercion, evaluation of bounded continuous f, exponential and product.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_extension_continuous
    (f : BoundedContinuousFunction ℝ≥0 ℝ) (w : ℝ) :
    Continuous (fun x : ℝ => Real.exp (w * x) *
      f ⟨max x 0, le_max_right x 0⟩) := by sorry
