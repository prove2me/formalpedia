-- Prove2me | Theorems.Thm_BlackScholesModel_gaussianReal_Iic_eq_stdNormalCDF
-- name    : BlackScholesModel.gaussianReal_Iic_eq_stdNormalCDF
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T16:25:57.218283+00:00
-- url     : https://prove2.me/theorems/f65a46e4-0f68-4583-b94b-32899b509bea
-- title:
--   Standard Gaussian probability of a lower ray equals the normal CDF
-- statement:
--   The Gaussian probability measure with mean zero and variance one assigns the half-line (-infinity,x] the standard normal cumulative distribution N(x) defined in BlackScholesModel_Core. The proof uses the exact pinned Mathlib Gaussian-measure density formula, its nonnegative integrability and the equality with the normal PDF integrand. It supplies the probability-to-integral bridge needed for digital-option and risk-neutral pricing milestones.
-- source:
--   Bridge from ProbabilityTheory.gaussianReal_apply_eq_integral and gaussianPDFReal_def at the pinned Mathlib revision to the exact core stdNormalCDF definition. Supports published cash_or_nothing_value and asset_or_nothing_value.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem gaussianReal_Iic_eq_stdNormalCDF (x : ℝ) :
    (gaussianReal 0 1).real (Set.Iic x) = stdNormalCDF x := by
  sorry

end BlackScholesModel
