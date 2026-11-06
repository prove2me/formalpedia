-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_foldRange
-- name    : ExplicitCost.Mirrors.foldRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:32:16.891088+00:00
-- url     : https://prove2.me/theorems/279a8704-5ae7-4b94-9f59-1b3e02ac4036
-- title:
--   Mirrors: fold Range
-- statement:
--   The loop over a range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L269-L286
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L269-L286

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

theorem ExplicitCost.Mirrors.foldRange [HasSize α] [HasSize α'] [HasSize γ] {M : QueryMachine Q A (α × ℕ) β} {M' : QueryMachine Q A (α' × ℕ) β} {w : α → α'} {d₁ dw d : ℕ} (hM : Mirrors M M' (Prod.map w id) d₁)
    {N : α → ℕ} {N' : α' → ℕ} (g : γ → ℕ → β → γ) {c₀ : α → γ} {c₀' : α' → γ} (hN : ∀ a, N' (w a) = N a) (hc : ∀ a, c₀' (w a) = c₀ a) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.foldRange N M g c₀) (QueryMachine.foldRange N' M' g c₀') w d := by sorry
