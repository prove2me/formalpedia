-- Prove2me | Theorems.Thm_ExplicitCost_bot_lists
-- name    : ExplicitCost.bot_lists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:12:34.757282+00:00
-- url     : https://prove2.me/theorems/4c8435ea-e989-4a90-aa15-fc03db6774ec
-- title:
--   Explicit Cost: bot lists
-- statement:
--   The function of the second pair of strings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L37-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L37-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowFactorRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.bot_lists (D : PiecesCounted.Data) (c : ℕ) (pad : U) (tr : Bool) (h j : ℕ) {s₁ s₂ θ : List Bool} (h1 : s₁.length = lam) :
    (piecesOf D c).bot ((pad, tr), (h, j), (s₁, s₂, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr true (indexAt D lam j) (PiecesCounted.toBits lam s₁, PiecesCounted.toBits lam s₂) θ else 0 := by sorry
