-- Prove2me | Theorems.Thm_ExplicitCost_Sizes_search_sizes
-- name    : ExplicitCost.Sizes.search_sizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:17:55.371248+00:00
-- url     : https://prove2.me/theorems/7c650d13-a61e-43eb-a1cb-2a4e890c284b
-- title:
--   Sizes: search sizes
-- statement:
--   With X = g(P+B), s the length of ζ and 1 ≤ K ≤ g: four copies of the input, four of K^g and 40
--   more units are at most (X + s)², hence at most (X + s)^10.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L99-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L99-L112

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
open ExplicitCost.Sizes

theorem ExplicitCost.Sizes.search_sizes {K g P B s sc sk : ℕ} (hK0 : 0 < K) (hKg : K ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) (hsc : sc ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B)) (hsk : sk ≤ g * g + 2) :
    4 * (s + (2 * K + 2 * g + 2 + sc)) + 4 * sk + 40 ≤ (g * (P + B) + s) ^ 10 := by sorry
