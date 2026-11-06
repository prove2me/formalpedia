-- Prove2me | Theorems.Thm_ExplicitCost_groupingWithCall
-- name    : ExplicitCost.groupingWithCall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:35:53.201218+00:00
-- url     : https://prove2.me/theorems/9d9a00ba-18cb-4f23-bdb2-c28d4046dd8e
-- title:
--   Explicit Cost: grouping With Call
-- statement:
--   **Lemma 8 up to the call.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L150-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L150-L151

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

theorem ExplicitCost.groupingWithCall : GroupingWithCall := by sorry
