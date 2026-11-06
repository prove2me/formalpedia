-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_ite
-- name    : ExplicitCost.Mirrors.ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:26:11.825079+00:00
-- url     : https://prove2.me/theorems/f80bd8ae-9d7e-4abd-980e-3af80fa6af9a
-- title:
--   Mirrors: ite
-- statement:
--   A choice by a test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L171-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L171-L176

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

theorem ExplicitCost.Mirrors.ite {M N : QueryMachine Q A α β} {M' N' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} (hM : Mirrors M M' w d) (hN : Mirrors N N' w d) {p : α → Bool} {p' : α' → Bool} (hp : ∀ a, p' (w a) = p a) :
    Mirrors (QueryMachine.ite p M N) (QueryMachine.ite p' M' N') w d := by sorry
