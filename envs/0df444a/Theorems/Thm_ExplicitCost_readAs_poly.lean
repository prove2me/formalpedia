-- Prove2me | Theorems.Thm_ExplicitCost_readAs_poly
-- name    : ExplicitCost.readAs_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:57.851296+00:00
-- url     : https://prove2.me/theorems/1b482439-4207-4262-ad25-e79bb9c51075
-- title:
--   Explicit Cost: read As poly
-- statement:
--   Answers read by a polynomial-time function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L99-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L99-L99

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

theorem ExplicitCost.readAs_poly {r : A' → A} (hr : PolyT r) {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) : (readAs r M).PolyTimeSteps := by sorry
