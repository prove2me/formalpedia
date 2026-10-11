-- Prove2me | Theorems.Thm_BlackScholesModel_gaussianReal_shifted_halfline
-- name    : BlackScholesModel.gaussianReal_shifted_halfline
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T17:20:53.914442+00:00
-- url     : https://prove2.me/theorems/1e4da893-53d6-4df8-b193-7cfaa4c9de9d
-- title:
--   Gaussian half-line probabilities with arbitrary mean
-- statement:
--   A Gaussian random variable with mean a and unit variance lies strictly above y with probability N(a-y) and strictly below y with probability N(y-a). This is the location-shift property of the Gaussian distribution and follows by mapping the standard Gaussian under the measurable translation z↦z+a, then applying the proved standard-Gaussian half-line probabilities. It separates the Gaussian shift step required by exponential tilting from the density calculation.
-- source:
--   Mathlib ProbabilityTheory.HasLaw.id and gaussianReal_add_const with the already Proved gaussianReal_halfline_probs. Supports gaussianReal_exponential_tilt_halfline and published asset-or-nothing pricing.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem gaussianReal_shifted_halfline (a y : ℝ) :
    (gaussianReal a 1).real (Set.Ioi y) = stdNormalCDF (a - y) ∧
    (gaussianReal a 1).real (Set.Iio y) = stdNormalCDF (y - a) := by
  sorry

end BlackScholesModel
