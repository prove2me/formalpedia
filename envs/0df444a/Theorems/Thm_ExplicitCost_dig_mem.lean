-- Prove2me | Theorems.Thm_ExplicitCost_dig_mem
-- name    : ExplicitCost.dig_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:47:32.107466+00:00
-- url     : https://prove2.me/theorems/acca1213-4e4e-4ba8-b122-ee0749b46a94
-- title:
--   Explicit Cost: dig mem
-- statement:
--   ι(q) is in 𝓘.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L54-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L54-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ParentNumbers
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowWeightRun
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.dig_mem {ρ : ℝ} {x₀ : ℕ} (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y q κ : ℕ) : indexAt D lam (digG (piecesOf D c) g tr 0 lam y q κ) ∈ (D.fam lam).I := by sorry
