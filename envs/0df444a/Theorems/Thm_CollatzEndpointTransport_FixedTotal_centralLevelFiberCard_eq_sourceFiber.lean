-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelFiberCard_eq_sourceFiber
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelFiberCard_eq_sourceFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:03.593671+00:00
-- url     : https://prove2.me/theorems/658a9299-cd6b-4f23-81d4-fa9cfa27c6dc
-- title:
--   Fixed Total: central Level Fiber Card eq source Fiber
-- statement:
--   The central mixed fiber is exactly the literal shell-source fiber.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L107-L145
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L107-L145

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq

theorem CollatzEndpointTransport.FixedTotal.centralLevelFiberCard_eq_sourceFiber
    (M s : ℕ) (theta eta : ℝ) (y : ℕ) :
    centralLevelFiberCard M s theta eta y =
      (mapFiber (centralLevelSourceSet M s theta eta)
        sourceEndpoint y).card := by sorry
