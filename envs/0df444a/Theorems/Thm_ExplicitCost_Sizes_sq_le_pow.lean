-- Prove2me | Theorems.Thm_ExplicitCost_Sizes_sq_le_pow
-- name    : ExplicitCost.Sizes.sq_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:22.027209+00:00
-- url     : https://prove2.me/theorems/eb7c3a34-dedf-4551-93a8-cfe328ea0ae4
-- title:
--   Sizes: sq le pow
-- statement:
--   256·X² ≤ X^{10} for X ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L83-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L83-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Cost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open ExplicitCost.Sizes

theorem ExplicitCost.Sizes.sq_le_pow {X : ℕ} (hX : 2 ≤ X) : 256 * (X * X) ≤ X ^ 10 := by sorry
