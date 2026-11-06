-- Prove2me | Theorems.Thm_ExplicitCost_total_le_gP
-- name    : ExplicitCost.total_le_gP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:58.044208+00:00
-- url     : https://prove2.me/theorems/a451430b-26cc-46a7-87ea-34f230d6b346
-- title:
--   Explicit Cost: total le g P
-- statement:
--   U ≤ gP, by (i) of Definition 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L105-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L105-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.total_le_gP {g : ℕ} {N : Net g} {P B : ℕ} (hN : N.Is P B) : N.U ≤ g * P := by sorry
