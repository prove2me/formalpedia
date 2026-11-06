-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_runs
-- name    : ExplicitCost.Mirrors.runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:09.745111+00:00
-- url     : https://prove2.me/theorems/3b649731-207d-41e6-955b-159f61078f08
-- title:
--   Mirrors: runs
-- statement:
--   **The same result, own steps and queries**, on states larger by at most d.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L55-L60

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

theorem ExplicitCost.Mirrors.runs {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (h : Mirrors M M' w d) {O : Q → Option A} {a : α} {own S : ℕ} {L : List Q} {b : β}
    (r : M.Runs O a own L S b) : M'.Runs O (w a) own L (S + d) b := by sorry
