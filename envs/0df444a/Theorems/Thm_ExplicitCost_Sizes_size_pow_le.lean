-- Prove2me | Theorems.Thm_ExplicitCost_Sizes_size_pow_le
-- name    : ExplicitCost.Sizes.size_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:17:15.473351+00:00
-- url     : https://prove2.me/theorems/7722c1b3-3c19-4080-9652-14660fe87263
-- title:
--   Sizes: size pow le
-- statement:
--   K^g has at most g² + 1 binary digits, for K ≤ g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L79-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingSearch.lean#L79-L84

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
import Theorems.Thm_ClauseBound_Gen_Rate_size_pow_le
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
open ExplicitCost.Sizes

theorem ExplicitCost.Sizes.size_pow_le {K g : ℕ} (hKg : K ≤ g) : size (K ^ g) ≤ g * g + 2 := by sorry
