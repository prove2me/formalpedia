-- Prove2me | Theorems.Thm_ExplicitCost_abs_value_le
-- name    : ExplicitCost.abs_value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:36:07.600026+00:00
-- url     : https://prove2.me/theorems/5a3ecc66-8b2b-4abb-97e3-efe2bc84ba4d
-- title:
--   Explicit Cost: abs value le
-- statement:
--   The value of a network: at most (2^P)^g terms, each a product of g values of the W_a and at most
--   g² values of the Ψ_{a,b}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L41-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingCall.lean#L41-L71

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
import Theorems.Thm_ClauseBound_Alg_Level_abs_value_le
import Theorems.Thm_Groundwork_Prog_abs_value_le

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.abs_value_le {g : ℕ} {N : Net g} {P B : ℕ} (h : N.Is P B) : |N.value| ≤ 2 ^ (g * P + g * B + g ^ 2 * B) := by sorry
