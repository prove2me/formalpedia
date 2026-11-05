-- Prove2me | Theorems.Thm_ExplicitCost_K_pos
-- name    : ExplicitCost.K_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:50:25.235169+00:00
-- url     : https://prove2.me/theorems/1532aa15-a87e-467f-b676-973b3f6bbf8a
-- title:
--   Explicit Cost: K pos
-- statement:
--   K_ℓ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L51-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
import Theorems.Thm_ClauseBound_Gen_Pick_K_pos

set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem ExplicitCost.K_pos (x₀ l : ℕ) : 1 ≤ Levels.Gen.K x₀ l := by sorry
