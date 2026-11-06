-- Prove2me | Theorems.Thm_ExplicitCost_subst_poly
-- name    : ExplicitCost.subst_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:01.485793+00:00
-- url     : https://prove2.me/theorems/bf8c8d2a-8d3c-447f-8368-901bc6ae932d
-- title:
--   Explicit Cost: subst poly
-- statement:
--   Queries answered by a machine with query access.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L93-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L93-L96

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

theorem ExplicitCost.subst_poly [HasSize C] [Enc C] [Carried C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (M.subst N).PolyTimeSteps := by sorry
