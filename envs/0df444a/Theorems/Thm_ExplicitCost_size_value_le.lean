-- Prove2me | Theorems.Thm_ExplicitCost_size_value_le
-- name    : ExplicitCost.size_value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:36:33.939378+00:00
-- url     : https://prove2.me/theorems/5bdd83f2-8ba5-4cc3-82c9-6ad5e1e19906
-- title:
--   Explicit Cost: size value le
-- statement:
--   The value of a network has at most gP + gB + g²B + 1 binary digits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L74-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L74-L81

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
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.size_value_le {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) : size N.value ≤ g * P + g * B + g ^ 2 * B + 2 := by sorry
