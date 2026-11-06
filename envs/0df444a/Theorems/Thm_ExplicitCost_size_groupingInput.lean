-- Prove2me | Theorems.Thm_ExplicitCost_size_groupingInput
-- name    : ExplicitCost.size_groupingInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:16:21.02839+00:00
-- url     : https://prove2.me/theorems/98f4a3dc-fd6d-4072-8d5a-ae91c9f8104c
-- title:
--   Explicit Cost: size grouping Input
-- statement:
--   The size of the input of the procedure.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L89-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L89-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_Exits_Runs
import Definitions.Def_Exits_Tested
import Definitions.Def_Eight_ViaGrouping_Search
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingSearch
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.size_groupingInput (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ) :
    size (groupingInput a b K N P B) = size (a, b) + (2 * K + 2 * g + 2 + size (netInput N P B)) := by sorry
