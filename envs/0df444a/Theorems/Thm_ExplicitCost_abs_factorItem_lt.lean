-- Prove2me | Theorems.Thm_ExplicitCost_abs_factorItem_lt
-- name    : ExplicitCost.abs_factorItem_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:12:56.254831+00:00
-- url     : https://prove2.me/theorems/e6a5c6e2-a29a-44c2-aa48-a3778e850466
-- title:
--   Explicit Cost: abs factor Item lt
-- statement:
--   It is below 2^{(2λ)^c} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L76-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L76-L81

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

theorem ExplicitCost.abs_factorItem_lt (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (hg : 0 < g) {q : FQ} (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) (j : ℕ) : |factorItem D c g tr lam y q j| < 2 ^ (2 * lam) ^ c := by sorry
