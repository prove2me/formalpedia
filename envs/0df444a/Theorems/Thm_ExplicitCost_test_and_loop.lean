-- Prove2me | Theorems.Thm_ExplicitCost_test_and_loop
-- name    : ExplicitCost.test_and_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:00.96248+00:00
-- url     : https://prove2.me/theorems/68d7adea-8dbe-4df0-8991-d30be65251cd
-- title:
--   Explicit Cost: test and loop
-- statement:
--   The test and the loop of `rowPair` written as products: over the g straight edges, and over the
--   pairs i < i'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternPsi.lean#L72-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternPsi.lean#L72-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternPsi
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.test_and_loop (g : ℕ) (tr : Bool) (lam : ℕ) (q : PsiQ) (F : ℕ → ℕ → ℤ) :
    (if straightOK g tr lam q = true then ∏ j ∈ range (g * g), (if j / g < j % g then F (j / g) (j % g) else 1) else 0) =
      (∏ i : Fin g, if heG g g lam q.2.1 i (nodeG g tr q.1.2 i) = heG g g lam q.2.2 i (nodeG g tr q.1.1 i) then 1 else 0) * ∏ k : Fin g × Fin g with k.1 < k.2, F k.1 k.2 := by sorry
