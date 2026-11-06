-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_prodRange
-- name    : ExplicitCost.Mirrors.prodRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:48:18.735051+00:00
-- url     : https://prove2.me/theorems/cf9d971f-c54c-4c2c-850c-63fa19af034c
-- title:
--   Mirrors: prod Range
-- statement:
--   The product over a range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L295-L298
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L295-L298

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}

theorem ExplicitCost.Mirrors.prodRange [HasSize α] [HasSize α'] {M : QueryMachine Q A (α × ℕ) ℤ} {M' : QueryMachine Q A (α' × ℕ) ℤ} {w : α → α'} {d₁ dw d : ℕ} (hM : Mirrors M M' (Prod.map w id) d₁)
    {N : α → ℕ} {N' : α' → ℕ} (hN : ∀ a, N' (w a) = N a) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.prodRange N M) (QueryMachine.prodRange N' M') w d := by sorry
