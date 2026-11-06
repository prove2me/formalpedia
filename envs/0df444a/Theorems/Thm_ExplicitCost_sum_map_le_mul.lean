-- Prove2me | Theorems.Thm_ExplicitCost_sum_map_le_mul
-- name    : ExplicitCost.sum_map_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:58:44.176225+00:00
-- url     : https://prove2.me/theorems/3f6df8eb-4008-4e06-accf-7c9ae72c1fcc
-- title:
--   Explicit Cost: sum map le mul
-- statement:
--   The sum of the prices of a list of queries, if every price is raised at most k times.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Answers.lean#L61-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Answers.lean#L61-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Answers
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed
variable {Q A A' α β : Type}

theorem ExplicitCost.sum_map_le_mul {w w' : Q → ℕ} {k : ℕ} (h : ∀ x, w' x ≤ k * w x) (L : List Q) : (L.map w').sum ≤ k * (L.map w).sum := by sorry
