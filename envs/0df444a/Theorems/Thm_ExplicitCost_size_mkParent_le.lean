-- Prove2me | Theorems.Thm_ExplicitCost_size_mkParent_le
-- name    : ExplicitCost.size_mkParent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:25:23.670707+00:00
-- url     : https://prove2.me/theorems/085fa680-82ee-41e9-b8a3-fd8d76dac12e
-- title:
--   Explicit Cost: size mk Parent le
-- statement:
--   **The size of a parent** is at most Ξ^{2c+4}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L90-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L90-L113

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

theorem ExplicitCost.size_mkParent_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {K g lam B y x : ℕ} (tr : Bool) (hK : K ≤ g) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B)
    (hy : y < #(D.fam lam).I ^ nRectG g g) (hx : x < K ^ g) : size (mkParent D K g lam B tr y x) ≤ Xi g lam B ^ (2 * c + 4) := by sorry
