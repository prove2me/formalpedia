-- Prove2me | Theorems.Thm_ExplicitCost_factor_eq
-- name    : ExplicitCost.factor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:25:43.267563+00:00
-- url     : https://prove2.me/theorems/52ea1d68-e80f-4f1c-bb6d-f2526197c17f
-- title:
--   Explicit Cost: factor eq
-- statement:
--   **f_{a,a'}(z, θ)** is the function `ClauseBound.Alg.gridFf` for the pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L83-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L83-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.factor_eq {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) :
    (patternNet D c g tr lam y W).f a b z θ = gridFf (piecesOf D c) [()] g g tr 0 lam y ((a.val, b.val), (z, θ)) := by sorry
