-- Prove2me | Theorems.Thm_ExplicitCost_labelLength_groupingInput
-- name    : ExplicitCost.labelLength_groupingInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:28.447567+00:00
-- url     : https://prove2.me/theorems/8645335b-bf22-4673-9b60-bf20c4c0fdf1
-- title:
--   Explicit Cost: label Length grouping Input
-- statement:
--   The number that the procedure computes, written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L78-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L78-L82

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
variable {P B}

theorem ExplicitCost.labelLength_groupingInput (hN : N.Is P B) :
    labelLength (groupingInput a b K N P B) = (b * N.U + 2 * min a b * g * P + b * K ^ 2 - 1) / (b * K ^ 2) := by sorry
