-- Prove2me | Theorems.Thm_ExplicitCost_mirrors_const
-- name    : ExplicitCost.mirrors_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:26:08.352067+00:00
-- url     : https://prove2.me/theorems/7073d698-0706-4699-9036-eb40549e7d49
-- title:
--   Explicit Cost: mirrors const
-- statement:
--   A constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L96-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L96-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}

theorem ExplicitCost.mirrors_const [HasSize α] [HasSize α'] [HasSize β] (b : β) {w : α → α'} {d : ℕ} (hw : ∀ a, size (w a) ≤ size a + d) :
    Mirrors (QueryMachine.const b : QueryMachine Q A α β) (QueryMachine.const b) w d := by sorry
