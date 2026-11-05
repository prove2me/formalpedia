-- Prove2me | Theorems.Thm_ExplicitCost_K_le_succ
-- name    : ExplicitCost.K_le_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:51:12.183445+00:00
-- url     : https://prove2.me/theorems/60c0d87a-0a9d-4e6a-949c-a8be50404b4c
-- title:
--   Explicit Cost: K le succ
-- statement:
--   K_ℓ ≤ K_{ℓ+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L57-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L57-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_succ

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem ExplicitCost.K_le_succ (x₀ l : ℕ) : Levels.Gen.K x₀ l ≤ Levels.Gen.K x₀ (l + 1) := by sorry
