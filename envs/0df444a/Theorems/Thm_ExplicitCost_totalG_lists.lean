-- Prove2me | Theorems.Thm_ExplicitCost_totalG_lists
-- name    : ExplicitCost.totalG_lists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:01.383668+00:00
-- url     : https://prove2.me/theorems/457d6c3a-a2ad-4ff8-9a34-cd09cbe4b5f3
-- title:
--   Explicit Cost: total G lists
-- statement:
--   The totals computed from the lists are those computed from the pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Totals.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Totals.lean#L42-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Totals
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}

theorem ExplicitCost.totalG_lists (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) (p d : ℕ) (tr : Bool) (y : ℕ) :
    totalG (listsAsPieces (listsOf D lam)) p d tr 0 lam y = totalG (piecesOf D c) p d tr 0 lam y := by sorry
