-- Prove2me | Theorems.Thm_ExplicitCost_groupingWithCallFrom
-- name    : ExplicitCost.groupingWithCallFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:36:25.272209+00:00
-- url     : https://prove2.me/theorems/c0654f73-ef8c-46ce-88c7-5a0ca4f43893
-- title:
--   Explicit Cost: grouping With Call From
-- statement:
--   How the search, its cost, the size bounds and the equality of the values (the clique of the
--   groups has the value of the network) give Lemma 8 up to the call.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L108-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L108-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Value_End
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingCall
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open Sizes

theorem ExplicitCost.groupingWithCallFrom : GroupingWithCallFrom := by sorry
