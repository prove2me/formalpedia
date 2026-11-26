-- Prove2me | Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_inner_pos
-- name    : CollatzEndpointTransport.OptimizedLinearPullback.psi_inner_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:47.920137+00:00
-- url     : https://prove2.me/theorems/89888c0b-b149-4450-a16f-8c62124c9551
-- title:
--   Optimized Linear Pullback: psi inner pos
-- statement:
--   The Optimized Linear Pullback construction uses the psi inner pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L43-L45
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L43-L45

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section

theorem CollatzEndpointTransport.OptimizedLinearPullback.psi_inner_pos (D : ℝ) :
    0 < (1 + Real.exp (-D * Real.log 3)) / 2 := by sorry
