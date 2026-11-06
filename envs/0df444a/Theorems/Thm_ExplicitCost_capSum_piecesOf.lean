-- Prove2me | Theorems.Thm_ExplicitCost_capSum_piecesOf
-- name    : ExplicitCost.capSum_piecesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:10.439195+00:00
-- url     : https://prove2.me/theorems/41b5284c-e136-4ed6-b422-4ffdb6c12bf2
-- title:
--   Explicit Cost: cap Sum pieces Of
-- statement:
--   c^row_i + c^col_i ≤ 4ρλ + c·log(2λ), for the largest of these sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Totals.lean#L34-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Totals.lean#L34-L39

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

theorem ExplicitCost.capSum_piecesOf (hS : Setting ρ c x₀ D) (h : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) : (capSum (piecesOf D c) h lam : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := by sorry
