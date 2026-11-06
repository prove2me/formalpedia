-- Prove2me | Theorems.Thm_ExplicitCost_capG_ofLists
-- name    : ExplicitCost.capG_ofLists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:40:53.474214+00:00
-- url     : https://prove2.me/theorems/caa99b7f-eb92-4feb-a02d-29b5de5398a6
-- title:
--   Explicit Cost: cap G of Lists
-- statement:
--   c_{a,a'}, from the lists and from the pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L65-L66

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

theorem ExplicitCost.capG_ofLists (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (p d : ℕ) (tr : Bool) (y a b : ℕ) : capG (listsAsPieces (listsOf D lam)) p d tr 0 lam y a b = capG (piecesOf D c) p d tr 0 lam y a b := by sorry
