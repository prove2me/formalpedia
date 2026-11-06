-- Prove2me | Theorems.Thm_ExplicitCost_size_listsOf_le
-- name    : ExplicitCost.size_listsOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:56.53264+00:00
-- url     : https://prove2.me/theorems/1572699f-1267-4fcb-8de2-d3e9b4830196
-- title:
--   Explicit Cost: size lists Of le
-- statement:
--   The three lists: at most (2λ)^c elements each; an element of 𝓘 has at most (2λ)^c bits, and
--   c^row_i, c^col_i ≤ 2λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L48-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L48-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentSize
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.size_listsOf_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {lam : ℕ} (hlam : 1 ≤ lam) :
    size (listsOf D lam) ≤ ((2 * lam) ^ c * ((2 * lam) ^ c + 1 + 1) + 1) + (((2 * lam) ^ c * (2 * lam + 1 + 1) + 1) + ((2 * lam) ^ c * (2 * lam + 1 + 1) + 1)) := by sorry
