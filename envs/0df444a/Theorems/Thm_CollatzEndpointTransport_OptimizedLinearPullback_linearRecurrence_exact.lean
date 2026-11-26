-- Prove2me | Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_linearRecurrence_exact
-- name    : CollatzEndpointTransport.OptimizedLinearPullback.linearRecurrence_exact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:48:36.525718+00:00
-- url     : https://prove2.me/theorems/5e2278ff-b041-466b-9f8d-56d5bb7393be
-- title:
--   Optimized Linear Pullback: linear Recurrence exact
-- statement:
--   Exact solution of `D_(j+1) = c D_j`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L183-L193
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/OptimizedLinearPullbackConstants.lean#L183-L193

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.OptimizedLinearPullback
open scoped Real Topology
noncomputable section

theorem CollatzEndpointTransport.OptimizedLinearPullback.linearRecurrence_exact
    (c D0 : ℝ) (D : ℕ → ℝ)
    (hD0 : D 0 = D0)
    (hstep : ∀ j, D (j + 1) = c * D j) :
    ∀ j, D j = c ^ j * D0 := by sorry
