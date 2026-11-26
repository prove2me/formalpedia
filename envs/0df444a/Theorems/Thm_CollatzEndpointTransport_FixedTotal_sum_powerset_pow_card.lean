-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_powerset_pow_card
-- name    : CollatzEndpointTransport.FixedTotal.sum_powerset_pow_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:38:54.681848+00:00
-- url     : https://prove2.me/theorems/eb5315b9-0404-5a39-ad0f-02e71cb3f25d
-- title:
--   Fixed Total: sum powerset pow card
-- statement:
--   Summing a weight depending only on subset cardinality gives the ordinary
--   binomial expansion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L149-L153
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L149-L153

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

theorem CollatzEndpointTransport.FixedTotal.sum_powerset_pow_card (U : Finset α) (t : ℝ) :
    ∑ J ∈ U.powerset, t ^ J.card = (1 + t) ^ U.card := by sorry
