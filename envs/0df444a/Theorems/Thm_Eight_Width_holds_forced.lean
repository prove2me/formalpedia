-- Prove2me | Theorems.Thm_Eight_Width_holds_forced
-- name    : Eight.Width.holds_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:49.274033+00:00
-- url     : https://prove2.me/theorems/a7c4bd03-6462-4154-be2a-1d943e95de30
-- title:
--   Width: holds forced
-- statement:
--   The three clauses say y = l₁ ∨ l₂.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L60-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L60-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}

theorem Eight.Width.holds_forced (a : V → Bool) (y : V) (l₁ l₂ : V × Bool) :
    Holds a (forced y l₁ l₂) ↔ (a y = true ↔ a l₁.1 = l₁.2 ∨ a l₂.1 = l₂.2) := by sorry
