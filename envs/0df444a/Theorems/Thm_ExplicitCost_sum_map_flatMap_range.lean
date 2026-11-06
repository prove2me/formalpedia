-- Prove2me | Theorems.Thm_ExplicitCost_sum_map_flatMap_range
-- name    : ExplicitCost.sum_map_flatMap_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:04:44.252943+00:00
-- url     : https://prove2.me/theorems/3df22560-d470-4070-b2de-53b1d636fa13
-- title:
--   Explicit Cost: sum map flat Map range
-- statement:
--   The prices of the queries of all rounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L90-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L90-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}

theorem ExplicitCost.sum_map_flatMap_range (w : Q → ℕ) (Lq : ℕ → List Q) (n : ℕ) : (((List.range n).flatMap Lq).map w).sum = ∑ y ∈ range n, ((Lq y).map w).sum := by sorry
