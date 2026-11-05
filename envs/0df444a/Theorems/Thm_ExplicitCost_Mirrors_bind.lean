-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_bind
-- name    : ExplicitCost.Mirrors.bind
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:47:21.234187+00:00
-- url     : https://prove2.me/theorems/ba4ce1b1-abb5-4703-84a4-d22764fd4ebc
-- title:
--   Mirrors: bind
-- statement:
--   One machine after the other. The first part runs beside a copy of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L179-L216
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L179-L216

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

theorem ExplicitCost.Mirrors.bind [HasSize α] [HasSize α'] {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {N : QueryMachine Q A (α × β) γ} {N' : QueryMachine Q A (α' × β) γ} {w : α → α'} {d₁ d₂ dw d : ℕ}
    (hM : Mirrors M M' w d₁) (hN : Mirrors N N' (Prod.map w id) d₂) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) (h2 : d₂ ≤ d) :
    Mirrors (QueryMachine.bind M N) (QueryMachine.bind M' N') w d := by sorry
