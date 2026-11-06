-- Prove2me | Theorems.Thm_ExplicitCost_foldRange_poly
-- name    : ExplicitCost.foldRange_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:16:46.127142+00:00
-- url     : https://prove2.me/theorems/541b857b-277d-4b3c-a489-030447f1731f
-- title:
--   Explicit Cost: fold Range poly
-- statement:
--   The loop over a range, if the range, the update and the start are polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L77-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L77-L80

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

theorem ExplicitCost.foldRange_poly [HasSize α] [Carried α] [HasSize γ] [Carried γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} (hN : PolyT N) (hM : M.PolyTimeSteps)
    (hg : PolyT fun p : γ × ℕ × β => g p.1 p.2.1 p.2.2) (hc : PolyT c₀) : (QueryMachine.foldRange N M g c₀).PolyTimeSteps := by sorry
