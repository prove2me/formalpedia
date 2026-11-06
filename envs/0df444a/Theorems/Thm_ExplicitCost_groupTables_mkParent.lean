-- Prove2me | Theorems.Thm_ExplicitCost_groupTables_mkParent
-- name    : ExplicitCost.groupTables_mkParent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:19:35.516966+00:00
-- url     : https://prove2.me/theorems/20510e95-bb00-487e-8f80-131730670576
-- title:
--   Explicit Cost: group Tables mk Parent
-- statement:
--   The tables W̃ of the callee, written with the numbers of the parent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L116-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L116-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.groupTables_mkParent (D : PiecesCounted.Data) (c K g lam B : ℕ) (tr : Bool) (y x L : ℕ) (W : ℕ → List Bool → ℤ) :
    groupTables D c (mkParent D K g lam B tr y x) L W = fun γ Θ => if h : γ < K then
      (Value.groupClique asked.under (netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) (patternNet D c g tr lam y W) (Nat.zero_lt_of_lt h) x L).W ⟨γ, h⟩ Θ else 0 := by sorry
