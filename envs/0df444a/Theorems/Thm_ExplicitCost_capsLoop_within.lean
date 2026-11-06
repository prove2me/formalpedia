-- Prove2me | Theorems.Thm_ExplicitCost_capsLoop_within
-- name    : ExplicitCost.capsLoop_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:51.761985+00:00
-- url     : https://prove2.me/theorems/531db603-11c4-4871-9fb6-5ca8c82d61d2
-- title:
--   Explicit Cost: caps Loop within
-- statement:
--   «The numbers … c^row_i, c^col_i are computed once»: if the oracle answers the question for the
--   element number j of the list by the number at the place j of `caps`, at the price t, the loop
--   returns `caps` within |𝓘|·(t + 1) operations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L95-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L95-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.capsLoop_within {σ : Type} [HasSize σ] {tr : Bool} {lamU : σ → List Unit} {idx : σ → List ℤ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {s : σ} (caps : List ℕ) (t : ℕ) (hlen : caps.length = (idx s).length)
    (hO : ∀ j < (idx s).length, O (Sum.inr (Sum.inr (lamU s, .inr (.inr (.inl (tr, (idx s).getD j 0)))))) = some (.inl (caps.getD j 0 : ℤ)))
    (hw : ∀ q, w (Sum.inr (Sum.inr (lamU s, q))) = t) :
    (capsLoop tr lamU idx).Within O w s ((idx s).length * (t + 1)) (2 * size s + 2 * size (idx s).length + 2 * size caps + 3) caps := by sorry
