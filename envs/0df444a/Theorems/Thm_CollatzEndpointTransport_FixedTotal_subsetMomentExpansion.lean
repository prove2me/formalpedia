-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_subsetMomentExpansion
-- name    : CollatzEndpointTransport.FixedTotal.subsetMomentExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:17.125071+00:00
-- url     : https://prove2.me/theorems/6b689077-fd18-560a-9b5d-87edcc1047f9
-- title:
--   Fixed Total: subset Moment Expansion
-- statement:
--   Exact factorial-moment expansion for the number of selected marked
--   positions.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L157-L174
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L157-L174

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

theorem CollatzEndpointTransport.FixedTotal.subsetMomentExpansion
    (U S : Finset α) (t : ℝ) :
    (1 + t) ^ (U ∩ S).card =
      ∑ J ∈ U.powerset, if J ⊆ S then t ^ J.card else 0 := by sorry
