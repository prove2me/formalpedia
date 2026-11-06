-- Prove2me | Theorems.Thm_ExplicitCost_Sizes_basic_facts
-- name    : ExplicitCost.Sizes.basic_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:55.698132+00:00
-- url     : https://prove2.me/theorems/f14b8c9c-51cf-4a0e-95fd-4f8cfb2f489e
-- title:
--   Sizes: basic facts
-- statement:
--   What is used of g, P, B: with q = P + B, X = g·q and A = g²·q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L89-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L89-L100

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

theorem ExplicitCost.Sizes.basic_facts {g P B : ℕ} (hg : 1 ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) :
    2 * g ≤ g * (P + B) ∧ P + B ≤ g * (P + B) ∧ g * g ≤ g * g * (P + B) ∧ g * g * P ≤ g * g * (P + B) ∧ B * (g * g) ≤ g * g * (P + B) ∧
      g * g * (P + B) ≤ g * (P + B) * (g * (P + B)) ∧ 2 * (g * (P + B)) ≤ g * (P + B) * (g * (P + B)) := by sorry
