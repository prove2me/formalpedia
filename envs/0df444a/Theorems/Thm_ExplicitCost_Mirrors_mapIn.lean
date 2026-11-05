-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_mapIn
-- name    : ExplicitCost.Mirrors.mapIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:19:20.842786+00:00
-- url     : https://prove2.me/theorems/0ad056fd-efa9-4c29-b030-9bf00977a40e
-- title:
--   Mirrors: map In
-- statement:
--   A function applied to the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L113-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L113-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}

theorem ExplicitCost.Mirrors.mapIn {M : QueryMachine Q A β γ} {M' : QueryMachine Q A β' γ} {w₂ : β → β'} {d : ℕ} (h : Mirrors M M' w₂ d) {g : α → β} {g' : α' → β'} {w : α → α'} (hg : ∀ a, g' (w a) = w₂ (g a)) :
    Mirrors (QueryMachine.mapIn g M) (QueryMachine.mapIn g' M') w d := by sorry
