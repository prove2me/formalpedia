-- Prove2me | Theorems.Thm_ExplicitCost_length_rectStrings
-- name    : ExplicitCost.length_rectStrings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:35.11542+00:00
-- url     : https://prove2.me/theorems/435e864b-cc3b-4909-a789-07fa28550a02
-- title:
--   Explicit Cost: length rect Strings
-- statement:
--   The four strings of a rectangle have λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L28-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L28-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.length_rectStrings {q : PsiQ} (ha : q.1.1 < nParts g g tr) (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hz' : q.2.2.length = nMemb g g tr * (g * g) * lam)
    {i i' : ℕ} (hi : i < nMemb g g tr) (hi' : i' < nMemb g g tr) :
    (rectStrings g tr lam q i i').1.length = lam ∧ (rectStrings g tr lam q i i').2.1.length = lam ∧ (rectStrings g tr lam q i i').2.2.1.length = lam ∧ (rectStrings g tr lam q i i').2.2.2.length = lam := by sorry
