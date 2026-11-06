-- Prove2me | Theorems.Thm_ExplicitCost_inU_groupingInput
-- name    : ExplicitCost.inU_groupingInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:27:15.001788+00:00
-- url     : https://prove2.me/theorems/d9dd924e-fa93-41cf-82c6-5af771efe52d
-- title:
--   Explicit Cost: in U grouping Input
-- statement:
--   The sum of the numbers c_{a,b} of the input is the total U.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L48-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L48-L52

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

theorem ExplicitCost.inU_groupingInput (hN : N.Is P B) : inU (groupingInput a b K N P B) = N.U := by sorry
