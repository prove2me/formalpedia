-- Prove2me | Theorems.Thm_ExplicitCost_lenG_ofLists
-- name    : ExplicitCost.lenG_ofLists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:41:06.443628+00:00
-- url     : https://prove2.me/theorems/da843c52-8cb3-48c2-a5ba-43981f454d81
-- title:
--   Explicit Cost: len G of Lists
-- statement:
--   The length of the chunk of a rectangle, from the lists and from the pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L61-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternIs
import Definitions.Def_Printed_GroupingProcs
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentNumbers
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.lenG_ofLists (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (d : ℕ) (tr : Bool) (y q κ : ℕ) : lenG (listsAsPieces (listsOf D lam)) d tr 0 lam y q κ = lenG (piecesOf D c) d tr 0 lam y q κ := by sorry
