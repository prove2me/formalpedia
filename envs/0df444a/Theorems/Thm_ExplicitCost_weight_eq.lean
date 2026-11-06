-- Prove2me | Theorems.Thm_ExplicitCost_weight_eq
-- name    : ExplicitCost.weight_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:25:36.512548+00:00
-- url     : https://prove2.me/theorems/c59b0d3c-0e8d-48d0-9c37-3d9931f9d5af
-- title:
--   Explicit Cost: weight eq
-- statement:
--   **W_a**, as `rowWeight` computes it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L53-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L53-L76

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

theorem ExplicitCost.weight_eq (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) :
    (patternNet D c g tr lam y W).W a z =
      if chkG g g tr lam (a.val, z) = true then ∏ i ∈ range (nMemb g g tr), W (toTable (pointQuery g tr lam (a.val, z) i)).1 (toTable (pointQuery g tr lam (a.val, z) i)).2 else 0 := by sorry
