-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_foldWhile
-- name    : ExplicitCost.Mirrors.foldWhile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:50:19.756439+00:00
-- url     : https://prove2.me/theorems/78949c61-98f9-4d27-800d-1b583767ace2
-- title:
--   Mirrors: fold While
-- statement:
--   The loop. The body runs beside the point of the loop, which holds a copy of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L219-L266
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L219-L266

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

theorem ExplicitCost.Mirrors.foldWhile [HasSize τ] [HasSize τ'] [HasSize γ] {M : QueryMachine Q A τ β} {M' : QueryMachine Q A τ' β} {wt : τ → τ'} {d₁ dw d : ℕ} (hM : Mirrors M M' wt d₁)
    {start : α → Option τ} {start' : α' → Option τ'} {nxt : τ → Option τ} {nxt' : τ' → Option τ'} {g : γ → τ → β → γ} {g' : γ → τ' → β → γ} {c₀ : α → γ} {c₀' : α' → γ} {w : α → α'}
    (hs : ∀ a, start' (w a) = (start a).map wt) (hn : ∀ t, nxt' (wt t) = (nxt t).map wt) (hg : ∀ c t b, g' c (wt t) b = g c t b) (hc : ∀ a, c₀' (w a) = c₀ a)
    (hw : ∀ t, size (wt t) ≤ size t + dw) (h1 : dw + d₁ ≤ d) :
    Mirrors (QueryMachine.foldWhile start nxt M g c₀) (QueryMachine.foldWhile start' nxt' M' g' c₀') w d := by sorry
