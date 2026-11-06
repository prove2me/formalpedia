-- Prove2me | Theorems.Thm_ExplicitCost_total_direction
-- name    : ExplicitCost.total_direction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:23.971693+00:00
-- url     : https://prove2.me/theorems/a45f345e-686c-437f-8310-408241ae60c0
-- title:
--   Explicit Cost: total direction
-- statement:
--   «the network with the smaller total»: its total is the smaller of the two.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L63-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L63-L74

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
variable (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ}

theorem ExplicitCost.total_direction (hl : hLev h = l + 1) (y : ℕ) :
    totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ h, y)) 0 (hLam h) y =
      min (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) false 0 (hLam h) y) (totalG (listsAsPieces (listsOf D (hLam h))) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) true 0 (hLam h) y) := by sorry
