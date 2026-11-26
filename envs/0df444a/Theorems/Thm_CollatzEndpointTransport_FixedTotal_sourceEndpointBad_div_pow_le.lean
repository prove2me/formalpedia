-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:25.698732+00:00
-- url     : https://prove2.me/theorems/0f7f2b3b-b45a-555a-a168-6ddadda6b788
-- title:
--   Fixed Total: source Endpoint Bad div pow le
-- statement:
--   Exact finite-shell nonlinear pullback before estimating the critical
--   information term.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L146-L223
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L146-L223

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M : ℕ) (hM : 1 ≤ M) (E : ℝ) (hE : 0 < E) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      C * E ^ 2 * Real.exp (-D * Real.log 3) *
          ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M +
        E⁻¹ * actualCriticalEndpointInformation M := by sorry
