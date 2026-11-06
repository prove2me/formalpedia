-- Prove2me | Theorems.Thm_ExplicitCost_groupTables_value
-- name    : ExplicitCost.groupTables_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:35.931381+00:00
-- url     : https://prove2.me/theorems/2ed70510-d72a-4beb-832a-8f35f43c6761
-- title:
--   Explicit Cost: group Tables value
-- statement:
--   The tables W̃, made an oracle and read back, give the value of the clique of the groups.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L65-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L65-L72

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

theorem ExplicitCost.groupTables_value (D : PiecesCounted.Data) (c : ℕ) (p : Parent) (L : ℕ) (W : ℕ → List Bool → ℤ) : ∀ hK0 : 0 < pK p,
    (clique (pK p) L fun w => readTables (answersOf (pK p) L (groupTables D c p L W)) w.val).value =
      (Value.groupClique asked.under (netInput (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) (netP p) (netB c p)) (patternNet D c (pG p) (pTr p) (pLam p) (pY p) W) hK0 (pX p) L).value := by sorry
