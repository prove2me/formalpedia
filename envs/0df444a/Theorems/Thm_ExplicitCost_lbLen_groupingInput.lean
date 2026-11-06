-- Prove2me | Theorems.Thm_ExplicitCost_lbLen_groupingInput
-- name    : ExplicitCost.lbLen_groupingInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:24:57.01427+00:00
-- url     : https://prove2.me/theorems/3d737cfb-7f35-4562-849f-5dfda5bc9b34
-- title:
--   Explicit Cost: lb Len grouping Input
-- statement:
--   The number of bits between two groups that the test forms from the input is Y_{γ,γ'}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L55-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingNumbers.lean#L55-L57

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

theorem ExplicitCost.lbLen_groupingInput (hK0 : 0 < K) (hN : N.Is P B) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g askedData.under.toPaperNetwork (groupingInput a b K N P B).2 x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' := by sorry
