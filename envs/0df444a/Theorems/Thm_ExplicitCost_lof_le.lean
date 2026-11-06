-- Prove2me | Theorems.Thm_ExplicitCost_lof_le
-- name    : ExplicitCost.lof_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:12.698207+00:00
-- url     : https://prove2.me/theorems/ad4e4cad-d5de-4f95-84f2-5d9e3826bf82
-- title:
--   Explicit Cost: lof le
-- statement:
--   L ≤ 3gP, crudely.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L89-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L89-L102

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

theorem ExplicitCost.lof_le {K g P U : ℕ} {ζ : ℝ} (hK : 1 ≤ K) (h0 : 0 ≤ ζ) (h1 : ζ ≤ 1) (hU : U ≤ g * P) : AppRunningTime.Lof K g ζ P U ≤ 3 * (g * P) := by sorry
