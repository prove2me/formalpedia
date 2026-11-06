-- Prove2me | Theorems.Thm_ExplicitCost_pLists_mk
-- name    : ExplicitCost.pLists_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:40:28.806959+00:00
-- url     : https://prove2.me/theorems/93271773-f9a0-4da0-ac4b-627e025ca5e7
-- title:
--   Explicit Cost: p Lists mk
-- statement:
--   Its lists.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L38-L38

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

theorem ExplicitCost.pLists_mk : pLists (mkParent D K g lam B tr y x) = listsOf D lam := by sorry
