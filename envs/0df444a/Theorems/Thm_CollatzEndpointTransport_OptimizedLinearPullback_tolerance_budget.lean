-- Prove2me | Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_tolerance_budget
-- name    : CollatzEndpointTransport.OptimizedLinearPullback.tolerance_budget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:48:36.445725+00:00
-- url     : https://prove2.me/theorems/d004e030-64c2-4606-a58f-fa173cbbb1f8
-- title:
--   Optimized Linear Pullback: tolerance budget
-- statement:
--   A parameterized version of the one-step tolerance budget.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L158-L169
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L158-L169

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section

theorem CollatzEndpointTransport.OptimizedLinearPullback.tolerance_budget
    {kappa t : ℝ}
    (hk : KappaAdmissible kappa)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * (kappa * t) + (kappa * t) ^ 2 ≤ t := by sorry
