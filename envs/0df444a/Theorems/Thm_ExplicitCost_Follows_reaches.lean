-- Prove2me | Theorems.Thm_ExplicitCost_Follows_reaches
-- name    : ExplicitCost.Follows.reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:47:06.728296+00:00
-- url     : https://prove2.me/theorems/604c9284-4ee5-40c1-b7d8-51a503fbab03
-- title:
--   Follows: reaches
-- statement:
--   A run from s gives a run from φ s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L47-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L47-L52

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

theorem ExplicitCost.Follows.reaches {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} {φ : M.σ → M'.σ} (h : Follows M M' w d φ) {O : Q → Option A} {S own : ℕ} {b : β} {s : M.σ} {L : List Q}
    (r : M.Reaches O S b s own L) : M'.Reaches O (S + d) b (φ s) own L := by sorry
