-- Prove2me | Theorems.Thm_ExplicitCost_withAlgorithm_poly
-- name    : ExplicitCost.withAlgorithm_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:19:43.497985+00:00
-- url     : https://prove2.me/theorems/67c1405a-d979-435e-8c2e-88fb7a1a724b
-- title:
--   Explicit Cost: with Algorithm poly
-- statement:
--   A machine with the queries to the pieces answered by an algorithm with polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyEnd.lean#L33-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyEnd.lean#L33-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_PolyProcedure
import Definitions.Def_CountedRecursion_PolySolver
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyEnd
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem ExplicitCost.withAlgorithm_poly {Q α β : Type} [HasSize Q] [Enc Q] [Carried Q] [Enc α] [Enc β] {M : QueryMachine (Q ⊕ PieceQuery) Ans α β} {Alg : Stepped PieceQuery Ans} (hM : M.PolyTimeSteps)
    (hA : Nonempty (IsPolyT Alg)) : (PiecesCounted.withAlgorithm M Alg).PolyTimeSteps := by sorry
