-- Prove2me | Theorems.Thm_ExplicitCost_Sizes_add_three_le
-- name    : ExplicitCost.Sizes.add_three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:35:50.134519+00:00
-- url     : https://prove2.me/theorems/6d74d4eb-7f1f-4ad9-9a02-9321236d0e7f
-- title:
--   Sizes: add three le
-- statement:
--   u + v + w ≤ Z^{n+2} if u, v, w ≤ Z^n and Z ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L86-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L86-L90

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
open ExplicitCost.Sizes

theorem ExplicitCost.Sizes.add_three_le {Z n u v w : ℕ} (hZ : 2 ≤ Z) (hu : u ≤ Z ^ n) (hv : v ≤ Z ^ n) (hw : w ≤ Z ^ n) : u + v + w ≤ Z ^ (n + 2) := by sorry
