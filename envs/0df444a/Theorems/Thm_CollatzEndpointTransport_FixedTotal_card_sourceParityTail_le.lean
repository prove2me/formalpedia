-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceParityTail_le
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceParityTail_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:04:45.079803+00:00
-- url     : https://prove2.me/theorems/52543255-96cd-41cb-9217-9b970919b87c
-- title:
--   Fixed Total: card source Parity Tail le
-- statement:
--   Exact source-code Hoeffding bound for the two-sided terminal parity
--   tail.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L778-L783
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L778-L783

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

theorem CollatzEndpointTransport.FixedTotal.card_sourceParityTail_le
    {M : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((sourceParityTail M t).card : ℝ) ≤
      (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * M)) := by sorry
