-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseSpend_lt_of_lt_length
-- name    : CollatzEndpointTransport.FixedTotal.reverseSpend_lt_of_lt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:27.788086+00:00
-- url     : https://prove2.me/theorems/1401c24d-6c21-4531-b017-c7726ee8fbfe
-- title:
--   Fixed Total: reverse Spend lt of lt length
-- statement:
--   A proper terminal segment has spend strictly below the total.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1018-L1032
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1018-L1032

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
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.reverseSpend_lt_of_lt_length
    {N : ℕ} (c : Composition N) {r : ℕ} (hr : r < c.length) :
    reverseSpend c r < N := by sorry
