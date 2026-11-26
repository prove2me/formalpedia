-- Prove2me | Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_hasDerivAt_psi
-- name    : CollatzEndpointTransport.OptimizedLinearPullback.hasDerivAt_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:44.7266+00:00
-- url     : https://prove2.me/theorems/d92d010d-a045-4455-b546-1e8f7de8c49e
-- title:
--   Optimized Linear Pullback: has Deriv At psi
-- statement:
--   Exact first derivative of the nonlinear rate.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L61-L90
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L61-L90

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section

theorem CollatzEndpointTransport.OptimizedLinearPullback.hasDerivAt_psi (D : ℝ) :
    HasDerivAt psi
      (Real.log 3 * Real.exp (-D * Real.log 3) /
        (1 + Real.exp (-D * Real.log 3))) D := by sorry
