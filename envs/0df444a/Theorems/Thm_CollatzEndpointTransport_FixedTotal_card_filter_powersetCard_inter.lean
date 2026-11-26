-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_filter_powersetCard_inter
-- name    : CollatzEndpointTransport.FixedTotal.card_filter_powersetCard_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:23.173832+00:00
-- url     : https://prove2.me/theorems/035abd8c-74d8-41bd-80ac-1f6c903ee694
-- title:
--   Fixed Total: card filter powerset Card inter
-- statement:
--   Subsets of fixed size and fixed marked intersection split uniquely into
--   their marked and unmarked parts.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L251-L352
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L251-L352

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
variable {α : Type*} [DecidableEq α]

theorem CollatzEndpointTransport.FixedTotal.card_filter_powersetCard_inter
    (V U : Finset α) {k j : ℕ}
    (hUV : U ⊆ V) (hjk : j ≤ k) :
    ((V.powersetCard k).filter fun S => (U ∩ S).card = j).card =
      U.card.choose j * (V.card - U.card).choose (k - j) := by sorry
