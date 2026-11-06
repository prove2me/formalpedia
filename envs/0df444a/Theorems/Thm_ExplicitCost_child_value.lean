-- Prove2me | Theorems.Thm_ExplicitCost_child_value
-- name    : ExplicitCost.child_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:05.723213+00:00
-- url     : https://prove2.me/theorems/b8894ee7-3f84-4eb6-b600-845dd66418a1
-- title:
--   Explicit Cost: child value
-- statement:
--   **The value of a callee** with the parent (K, g, λ, B, the lists, tr, y, x) and the label length
--   L: the value of the (K, L)-clique of the groups of the grouping x of the network of the pattern y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L76-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L76-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.child_value (D : PiecesCounted.Data) (c x₀ : ℕ) (Bound : Ctx → Prop) (a' : Ctx) (f : TableQuery → Option Ans) {K g lam B L y x : ℕ} {tr : Bool} (hK : Levels.Gen.K x₀ (cLev a') = K)
    (hp : parentOf a' = mkParent D K g lam B tr y x) (hL : cLam a' = L) (hK0 : 0 < K) :
    (spec D c x₀ Bound).val a' ((spec D c x₀ Bound).tab a' f) =
      .inl (Value.groupClique asked.under (netInput (patternNet D c g tr lam y (readTables f)) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y (readTables f)) hK0 x L).value := by sorry
