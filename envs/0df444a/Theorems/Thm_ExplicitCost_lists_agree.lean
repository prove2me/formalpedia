-- Prove2me | Theorems.Thm_ExplicitCost_lists_agree
-- name    : ExplicitCost.lists_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:46:05.85714+00:00
-- url     : https://prove2.me/theorems/f7573fd3-66ee-4fe1-937c-7b50308cb831
-- title:
--   Explicit Cost: lists agree
-- statement:
--   What the congruence lemmas ask.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L46-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L46-L54

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

theorem ExplicitCost.lists_agree (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) :
    (listsAsPieces (listsOf D lam)).cnt 0 lam = (piecesOf D c).cnt 0 lam ∧ 1 ≤ (listsAsPieces (listsOf D lam)).cnt 0 lam ∧
      ∀ tr, ∀ j < (listsAsPieces (listsOf D lam)).cnt 0 lam, (listsAsPieces (listsOf D lam)).cap tr 0 lam j = (piecesOf D c).cap tr 0 lam j := by sorry
