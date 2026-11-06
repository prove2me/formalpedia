-- Prove2me | Theorems.Thm_ExplicitCost_ofFun_poly
-- name    : ExplicitCost.ofFun_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:13:46.04938+00:00
-- url     : https://prove2.me/theorems/66b5d70b-4286-4cdb-9d99-6544efd9920e
-- title:
--   Explicit Cost: of Fun poly
-- statement:
--   One step that applies a polynomial-time function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L33-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]

theorem ExplicitCost.ofFun_poly [HasSize α] [HasSize β] [Carried α] [Carried β] {f : α → β} (hf : PolyT f) : (QueryMachine.lift (Stepped.ofFun f) : QueryMachine Q A α β).PolyTimeSteps := by sorry
