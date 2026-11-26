-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceLateFirstOdd_le
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceLateFirstOdd_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:03:28.699837+00:00
-- url     : https://prove2.me/theorems/08d80bf3-12bc-5995-b8bb-213d24f9df0e
-- title:
--   Fixed Total: card source Late First Odd le
-- statement:
--   A coarse polynomial-times-geometric bound for late first-odd
--   positions.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L860-L878
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L860-L878

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_sourceLateFirstOdd_le
    {M K : ℕ} (hKM : K ≤ M) :
    (sourceLateFirstOdd M K).card ≤
      (M + 1) * 2 ^ (M - K) := by sorry
