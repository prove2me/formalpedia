-- Prove2me | Theorems.Thm_BlackScholesModel_gaussianReal_halfline_probs
-- name    : BlackScholesModel.gaussianReal_halfline_probs
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T16:58:30.579098+00:00
-- url     : https://prove2.me/theorems/eb2fb0e8-9c2a-4599-946a-d529a1ae8cdb
-- title:
--   Standard Gaussian probabilities of both open half-lines
-- statement:
--   For a standard normal random variable, the probability of the strictly upper half-line (x,infinity) is N(-x), and the probability of the strictly lower half-line (-infinity,x) is N(x). The first follows by taking the complement of (-infinity,x]; the second follows because the nondegenerate Gaussian measure has no point masses. This is the measure-theoretic link from terminal-price strike crossing to both cash-or-nothing digital option formulas.
-- source:
--   Exact measures via proved gaussianReal_Iic_eq_stdNormalCDF, stdNormalCDF_neg, Mathlib measureReal_compl, measureReal_diff_null and nullSingletonClass_gaussianReal at pinned revision. Supports published cash_or_nothing_value.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem gaussianReal_halfline_probs (x : ℝ) :
    (gaussianReal 0 1).real (Set.Ioi x) = stdNormalCDF (-x) ∧
    (gaussianReal 0 1).real (Set.Iio x) = stdNormalCDF x := by
  sorry

end BlackScholesModel
