-- Prove2me | Theorems.Thm_ExplicitCost_inB_groupingInput
-- name    : ExplicitCost.inB_groupingInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:24:25.278236+00:00
-- url     : https://prove2.me/theorems/fdc2ef8f-1bf5-406b-85af-31e8b538b505
-- title:
--   Explicit Cost: in B grouping Input
-- statement:
--   The B of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L43-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L43-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingNumbers
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ)

theorem ExplicitCost.inB_groupingInput : inB (groupingInput a b K N P B) = B := by sorry
