-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_nonlinear
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_nonlinear
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:36:29.230562+00:00
-- url     : https://prove2.me/theorems/844e1842-484d-4aff-8ef0-b38e9ea84faf
-- title:
--   Fixed Total: source Endpoint Bad div pow le nonlinear
-- statement:
--   The exact nonlinear shell estimate after the optimal balanced
--   heavy-fiber threshold `E = exp (psi(D) M / 3)`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L248-L308
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L248-L308

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_nonlinear
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (hM : 1 ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      (C * Real.exp (-D * Real.log 3) +
          9 * Real.sqrt 3 * (M : ℝ) * Real.sqrt M) *
        Real.exp
          (-(OptimizedLinearPullback.psi D / 3) * M) := by sorry
