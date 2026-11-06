-- Prove2me | Theorems.Thm_ExplicitCost_mem_S_iff
-- name    : ExplicitCost.mem_S_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:25:23.67054+00:00
-- url     : https://prove2.me/theorems/f908a54a-40b3-4b51-bd07-e08b6d485ae0
-- title:
--   Explicit Cost: mem S iff
-- statement:
--   The settings of a row are the strings of g·g²·λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L39-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.mem_S_iff (a : Fin (nParts g g tr)) (z : List Bool) : z ∈ (patternNet D c g tr lam y W).S a ↔ z.length = nMemb g g tr * (g * g) * lam := by sorry
