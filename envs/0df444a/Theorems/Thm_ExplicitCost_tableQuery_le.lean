-- Prove2me | Theorems.Thm_ExplicitCost_tableQuery_le
-- name    : ExplicitCost.tableQuery_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:23:19.853679+00:00
-- url     : https://prove2.me/theorems/c788229b-a894-4653-bc12-8ed5872fe7c2
-- title:
--   Explicit Cost: table Query le
-- statement:
--   With 4 more this is at most the bound on the sizes, for every C₀ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L94-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L94-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndBounds
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.tableQuery_le {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {C : ℕ} (hC : 1 ≤ C) :
    ((Levels.Gen.K x₀ l + 2 * Levels.Gen.K x₀ l * lam + B + 3 + 4 : ℕ) : ℝ) ≤ sizeBound x₀ C l lam B := by sorry
