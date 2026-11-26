-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceParityTail_eq
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceParityTail_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:48.971702+00:00
-- url     : https://prove2.me/theorems/bb8bb313-8f1e-46d0-97a6-c3c1082c530d
-- title:
--   Fixed Total: card source Parity Tail eq
-- statement:
--   The source-code parity tail has the same cardinality as the exact
--   residue tail supplied by the Terras bijection.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L728-L774
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L728-L774

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

theorem CollatzEndpointTransport.FixedTotal.card_sourceParityTail_eq
    (M : ℕ) (t : ℝ) :
    (sourceParityTail M t).card =
      (Terras.shellParityPrefixBadAt M M t).card := by sorry
