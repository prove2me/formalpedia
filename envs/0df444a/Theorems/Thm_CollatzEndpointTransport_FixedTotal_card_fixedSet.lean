-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
-- name    : CollatzEndpointTransport.FixedTotal.card_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:50.96213+00:00
-- url     : https://prove2.me/theorems/6f233292-90ce-5cda-9071-f1cb1167fc05
-- title:
--   Fixed Total: card fixed Set
-- statement:
--   A composition of `N` has `s` parts in exactly `choose (N-1) (s-1)` ways.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L336-L374
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L336-L374

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_fixedSet
    (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    (fixedSet N s).card = (N - 1).choose (s - 1) := by sorry
