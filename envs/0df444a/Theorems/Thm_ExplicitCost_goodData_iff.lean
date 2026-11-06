-- Prove2me | Theorems.Thm_ExplicitCost_goodData_iff
-- name    : ExplicitCost.goodData_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:31:55.579447+00:00
-- url     : https://prove2.me/theorems/7fe46078-bffc-4892-b250-6e7f27fbbf52
-- title:
--   Explicit Cost: good Data iff
-- statement:
--   The test of the procedure says yes to y exactly if the grouping number y has the two properties.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L36-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L36-L57

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

theorem ExplicitCost.goodData_iff {a b K g : ℕ} (hK0 : 0 < K) {N : Net g} {P B : ℕ} (hb : 0 < b) (hab : a ≤ b) (hN : N.Is P B) (y : ℕ) :
    goodData (groupingInput a b K N P B, y) = true ↔
      (∀ γ : Fin K, K * #{v : Fin g | Paper.grouping hK0 y v = γ} ≤ 2 * g) ∧ ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 y) γ γ' ≤ AppRunningTime.Lof K g ((a : ℝ) / b) P N.U := by sorry
