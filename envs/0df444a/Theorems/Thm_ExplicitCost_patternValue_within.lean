-- Prove2me | Theorems.Thm_ExplicitCost_patternValue_within
-- name    : ExplicitCost.patternValue_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:50.070739+00:00
-- url     : https://prove2.me/theorems/3970a909-f422-4f78-93c9-367fdca54db9
-- title:
--   Explicit Cost: pattern Value within
-- statement:
--   The call of the procedure of the lemma is passed on as a call of the solver, at two operations
--   more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L37-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L37-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.patternValue_within (hSub : QueryMachines.StSubstWithin) {c : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {v : Ready × ℕ} {x tc T Sg : ℕ} {Z Zc : ℤ}
    (hG : ∀ O' : CliqueCall → Option ℤ, O' (callOf (searchInput c v, x)) = some Zc → groupingCall.Within O' (fun _ => tc + 2) (searchInput c v) T Sg Z)
    (hO : O (Sum.inl (child (v, callOf (searchInput c v, x)))) = some (.inl Zc)) (hw : w (Sum.inl (child (v, callOf (searchInput c v, x)))) = tc) :
    (patternValue c).Within O w v T (size v + Sg + (max (size (v, callOf (searchInput c v, x))) (size (Sum.inl Zc : Ans)) + 1) + 1) Z := by sorry
