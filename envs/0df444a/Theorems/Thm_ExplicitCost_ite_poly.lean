-- Prove2me | Theorems.Thm_ExplicitCost_ite_poly
-- name    : ExplicitCost.ite_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:12.826623+00:00
-- url     : https://prove2.me/theorems/d0b65bc1-ae06-48f6-8fad-4c4a8e71a2c5
-- title:
--   Explicit Cost: ite poly
-- statement:
--   A choice by a polynomial-time test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L68-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L68-L71

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

theorem ExplicitCost.ite_poly {p : α → Bool} (hp : PolyT p) {M N : QueryMachine Q A α β} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (QueryMachine.ite p M N).PolyTimeSteps := by sorry
