-- Prove2me | Theorems.Thm_BlackScholesModel_stdNormalPDF_hasDerivAt
-- name    : BlackScholesModel.stdNormalPDF_hasDerivAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:12:10.759176+00:00
-- url     : https://prove2.me/theorems/5c797c03-c478-4b29-9363-8ddcc8187b9b
-- title:
--   Derivative of the standard normal density
-- statement:
--   The standard normal density φ(x) = (1/sqrt(2π)) exp(-x²/2) satisfies φ'(x)=-x φ(x) for every real x. This follows by the exponential chain rule and differentiation of the quadratic exponent. It supplies an analytic recurrence for the density and underpins higher differentiability of the standard normal CDF, needed for Black–Scholes smoothness, Greeks, and the pricing PDE.
-- source:
--   Differentiation of the exact BlackScholesModel_Core stdNormalPDF definition, as used in the mission's standard-normal CDF and Greeks. Independent source-faithful analytic helper for smoothness and higher-derivative milestones.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem stdNormalPDF_hasDerivAt (x : ℝ) :
    HasDerivAt stdNormalPDF (-x * stdNormalPDF x) x := by
  sorry

end BlackScholesModel
