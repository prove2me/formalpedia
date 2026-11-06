-- Prove2me | Theorems.Thm_ExplicitCost_abs_pairItem_lt
-- name    : ExplicitCost.abs_pairItem_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:04:19.714328+00:00
-- url     : https://prove2.me/theorems/5babcc0e-adfc-4a4d-9481-2fbd97ea5616
-- title:
--   Explicit Cost: abs pair Item lt
-- statement:
--   It is below 2^{(2λ)^c} in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L66-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L66-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.abs_pairItem_lt (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (q : PsiQ) (j : ℕ) : |pairItem D c g tr lam y q j| < 2 ^ (2 * lam) ^ c := by sorry
