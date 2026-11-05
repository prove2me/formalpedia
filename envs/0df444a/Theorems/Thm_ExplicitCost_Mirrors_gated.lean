-- Prove2me | Theorems.Thm_ExplicitCost_Mirrors_gated
-- name    : ExplicitCost.Mirrors.gated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:26:39.094172+00:00
-- url     : https://prove2.me/theorems/c70f56ca-eb45-41eb-bd67-7bd905ad6651
-- title:
--   Mirrors: gated
-- statement:
--   A machine behind a test. The test runs beside a copy of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L301-L310
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Mirror.lean#L301-L310

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

theorem ExplicitCost.Mirrors.gated [HasSize α] [HasSize α'] {M : QueryMachine Q A α Bool} {M' : QueryMachine Q A α' Bool} {N : QueryMachine Q A α ℤ} {N' : QueryMachine Q A α' ℤ} {w : α → α'} {d₁ d₂ dw d : ℕ}
    (hM : Mirrors M M' w d₁) (hN : Mirrors N N' w d₂) (hw : ∀ a, size (w a) ≤ size a + dw) (h1 : dw + d₁ ≤ d) (h2 : d₂ ≤ d) :
    Mirrors (QueryMachine.gated M N) (QueryMachine.gated M' N') w d := by sorry
