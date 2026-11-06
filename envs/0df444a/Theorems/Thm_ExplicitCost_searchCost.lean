-- Prove2me | Theorems.Thm_ExplicitCost_searchCost
-- name    : ExplicitCost.searchCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:19.489996+00:00
-- url     : https://prove2.me/theorems/4a5d5da7-d3d7-4a5a-b0f6-b1dd52f953d5
-- title:
--   Explicit Cost: search Cost
-- statement:
--   The search takes at most 10·K^g steps, on states of size at most (g(P+B) + the length of
--   ζ)^{10}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L120-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L120-L143

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
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open Sizes

theorem ExplicitCost.searchCost : SearchCost := by sorry
