-- Prove2me | Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_tendsto_psi_div_zero_right
-- name    : CollatzEndpointTransport.OptimizedLinearPullback.tendsto_psi_div_zero_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:38:51.78255+00:00
-- url     : https://prove2.me/theorems/7746d9d0-7beb-4801-9043-4e582f78872d
-- title:
--   Optimized Linear Pullback: tendsto psi div zero right
-- statement:
--   The critical small-density slope:
--   `psi(D)/D -> log(3)/2` from the right.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L100-L106
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L100-L106

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section

theorem CollatzEndpointTransport.OptimizedLinearPullback.tendsto_psi_div_zero_right :
    Filter.Tendsto (fun D : ℝ => psi D / D)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 3 / 2)) := by sorry
