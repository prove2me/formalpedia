-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_mapOut
-- name    : ExplicitCost.Mirrors.mapOut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:46:42.957906+00:00
-- url     : https://prove2.me/theorems/65685622-99d9-4fbc-90a2-35f4c3e25a4b
-- title:
--   Mirrors: map Out
-- statement:
--   A function applied to the result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L123-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L123-L129

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

theorem ExplicitCost.Mirrors.mapOut {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) (g : β → γ) :
    Mirrors (QueryMachine.mapOut M g) (QueryMachine.mapOut M' g) w d := by sorry
