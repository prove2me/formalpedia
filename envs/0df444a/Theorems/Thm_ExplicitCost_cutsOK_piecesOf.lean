-- Prove2me | Theorems.Thm_ExplicitCost_cutsOK_piecesOf
-- name    : ExplicitCost.cutsOK_piecesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:44.750201+00:00
-- url     : https://prove2.me/theorems/b012e565-cacd-40cf-bf44-06f1b460f91d
-- title:
--   Explicit Cost: cuts OK pieces Of
-- statement:
--   The pieces factor as the grid of this development asks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternPsi.lean#L33-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternPsi.lean#L33-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternPsi
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.cutsOK_piecesOf {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) (pad : U) :
    CutsOK (piecesOf D c) pad 0 lam fun j => (D.fam lam).A (indexAt D lam j) := by sorry
