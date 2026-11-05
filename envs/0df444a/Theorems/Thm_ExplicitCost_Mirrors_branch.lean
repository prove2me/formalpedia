-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_branch
-- name    : ExplicitCost.Mirrors.branch
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:47:45.310021+00:00
-- url     : https://prove2.me/theorems/9a0f6dbd-f17d-4a50-9d8c-6940add0a66f
-- title:
--   Mirrors: branch
-- statement:
--   A choice between two machines.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L132-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L132-L168

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

theorem ExplicitCost.Mirrors.branch {M₁ : QueryMachine Q A α₁ β} {M₁' : QueryMachine Q A α₁' β} {M₂ : QueryMachine Q A α₂ β} {M₂' : QueryMachine Q A α₂' β} {w₁ : α₁ → α₁'} {w₂ : α₂ → α₂'} {d : ℕ}
    (h₁ : Mirrors M₁ M₁' w₁ d) (h₂ : Mirrors M₂ M₂' w₂ d) {sel : α → α₁ ⊕ α₂} {sel' : α' → α₁' ⊕ α₂'} {w : α → α'} (hs : ∀ a, sel' (w a) = Sum.map w₁ w₂ (sel a)) :
    Mirrors (QueryMachine.branch sel M₁ M₂) (QueryMachine.branch sel' M₁' M₂') w d := by sorry
