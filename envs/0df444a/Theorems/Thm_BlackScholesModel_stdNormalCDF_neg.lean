-- Prove2me | Theorems.Thm_BlackScholesModel_stdNormalCDF_neg
-- name    : BlackScholesModel.stdNormalCDF_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T12:06:27.13899+00:00
-- url     : https://prove2.me/theorems/587b31c5-e953-4fbf-9879-4358d8c6009f
-- title:
--   Standard normal CDF symmetry about zero
-- statement:
--   For a standard normal random variable, symmetry about zero gives N(-x)=1-N(x) for every real x. This identity is the analytic normal-CDF symmetry needed to prove put–call parity simultaneously in spot and forward formulations, because call and put pricing formulas involve N(d) and N(-d). It can be established by changing variables in the Gaussian integral and using that the standard normal density is even and integrates to one.
-- source:
--   Mathematical normal-distribution symmetry underlying the put–call parity formulas, in Black–Scholes Model: Pricing Formula, PDE and Greeks. Source: standard Gaussian symmetry, used in the textbook Black–Scholes call/put equations. Intended reusable formal helper for mission milestones put_call_parity and put_call_parity_fwd, whose exact statements are independently published.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem stdNormalCDF_neg (x : ℝ) :
    stdNormalCDF (-x) = 1 - stdNormalCDF x := by
  sorry

end BlackScholesModel
