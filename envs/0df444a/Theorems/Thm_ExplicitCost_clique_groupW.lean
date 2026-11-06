-- Prove2me | Theorems.Thm_ExplicitCost_clique_groupW
-- name    : ExplicitCost.clique_groupW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:38:59.499198+00:00
-- url     : https://prove2.me/theorems/55611df8-ff44-44dc-aa7e-c778c85b07bf
-- title:
--   Explicit Cost: clique group W
-- statement:
--   The clique with these tables is the clique of the groups.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingLemma.lean#L102-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingLemma.lean#L102-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_Achievable
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingLemma
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes

theorem ExplicitCost.clique_groupW {g K : ℕ} (N : Net g) (P B : ℕ) (hK0 : 0 < K) (x L : ℕ) :
    (clique K L fun w => groupW N P B hK0 x L w.val) = Value.groupClique asked.under (netInput N P B) N hK0 x L := by sorry
