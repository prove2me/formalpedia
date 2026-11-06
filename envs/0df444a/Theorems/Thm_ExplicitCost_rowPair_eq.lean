-- Prove2me | Theorems.Thm_ExplicitCost_rowPair_eq
-- name    : ExplicitCost.rowPair_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:43.961763+00:00
-- url     : https://prove2.me/theorems/f7a4ad25-66b5-4ee1-84e6-80f8c2deeaa8
-- title:
--   Explicit Cost: row Pair eq
-- statement:
--   `rowPair` puts the query in order and runs the loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L59-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L59-L59

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

theorem ExplicitCost.rowPair_eq : rowPair = QueryMachine.mapIn (fun x : Parent × PsiQ => (x.1, ordered x.2)) pairLoop := by sorry
