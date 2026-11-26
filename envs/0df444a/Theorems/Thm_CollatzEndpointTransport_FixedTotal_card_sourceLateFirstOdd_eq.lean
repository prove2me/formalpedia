-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceLateFirstOdd_eq
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceLateFirstOdd_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:54.939948+00:00
-- url     : https://prove2.me/theorems/322fb543-3136-5db0-b5c9-bdc56d7aa912
-- title:
--   Fixed Total: card source Late First Odd eq
-- statement:
--   Exact geometric count of the late-first-odd remainder.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L826-L856
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L826-L856

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

theorem CollatzEndpointTransport.FixedTotal.card_sourceLateFirstOdd_eq
    (M K : ℕ) :
    (sourceLateFirstOdd M K).card =
      1 + ∑ u : Fin M,
        if K ≤ (u : ℕ) then 2 ^ (M - (u : ℕ) - 1) else 0 := by sorry
