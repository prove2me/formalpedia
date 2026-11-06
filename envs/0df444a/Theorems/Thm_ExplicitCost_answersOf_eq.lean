-- Prove2me | Theorems.Thm_ExplicitCost_answersOf_eq
-- name    : ExplicitCost.answersOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:05:43.290872+00:00
-- url     : https://prove2.me/theorems/c998ec43-a197-4ff4-8cd0-8e0fe4f32da7
-- title:
--   Explicit Cost: answers Of eq
-- statement:
--   A legitimate query to the tables is answered by the entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L48-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L48-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ParentNumbers
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowWeightRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.answersOf_eq {K : ℕ} {q : TableQuery} (h1 : q.1 < K) (h2 : q.2.length = (K - 1) * lam) : answersOf K lam W q = some (Sum.inl (W q.1 q.2)) := by sorry
