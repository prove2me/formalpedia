-- Prove2me | Theorems.Thm_ExplicitCost_inK_groupingInput
-- name    : ExplicitCost.inK_groupingInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:55.548365+00:00
-- url     : https://prove2.me/theorems/deedfe1b-7066-491a-9cbe-1e24cf5c9dc3
-- title:
--   Explicit Cost: in K grouping Input
-- statement:
--   The K of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L34-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L34-L34

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

theorem ExplicitCost.inK_groupingInput : inK (groupingInput a b K N P B) = K := by sorry
