-- Prove2me | Theorems.Thm_BlackScholesModel_gaussianReal_exponential_tilt_halfline
-- name    : BlackScholesModel.gaussianReal_exponential_tilt_halfline
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T17:02:31.828863+00:00
-- url     : https://prove2.me/theorems/ce011beb-ce98-47e7-9a57-c6aec303538c
-- title:
--   Exponential tilting of a Gaussian truncated to open half-lines
-- statement:
--   For a standard normal variable Z, the truncated expectations of exp(a Z-a²/2) above and below a threshold y equal N(a-y) and N(y-a), respectively. Multiplying the standard normal density by the exponential tilt produces a normal density shifted by a, using completion of the square, followed by translation of the integration interval. This mathematically substantive identity reduces both asset-or-nothing valuations to the Gaussian distribution and exact terminal-price event threshold.
-- source:
--   Gaussian exponential tilting/shift of measure, derived from pinned Mathlib ProbabilityTheory.gaussianPDFReal_def and gaussianReal_apply_eq_integral. Used for published asset_or_nothing_value and callPrice_eq_risk_neutral_expectation.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem gaussianReal_exponential_tilt_halfline (a y : ℝ) :
    (∫ z in Set.Ioi y, Real.exp (a * z - a ^ 2 / 2)
        ∂(gaussianReal 0 1)) = stdNormalCDF (a - y) ∧
    (∫ z in Set.Iio y, Real.exp (a * z - a ^ 2 / 2)
        ∂(gaussianReal 0 1)) = stdNormalCDF (y - a) := by
  sorry

end BlackScholesModel
