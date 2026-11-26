-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelBadMass_cast_le
-- name    : CollatzEndpointTransport.FixedTotal.actualLevelBadMass_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:45.439929+00:00
-- url     : https://prove2.me/theorems/55143ba9-97a7-4b5f-a134-2c0a2e1a2685
-- title:
--   Fixed Total: actual Level Bad Mass cast le
-- statement:
--   One odd-count level after inserting the `(C,D)` target bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L76-L142
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L76-L142

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.actualLevelBadMass_cast_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (E : ℝ)
    (hE : 0 < E) (hs : s ≤ M) :
    (actualLevelBadMass S M s : ℝ) ≤
      C * E ^ 2 * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        E⁻¹ * Real.sqrt 3 *
          actualLevelCriticalContribution M s := by sorry
