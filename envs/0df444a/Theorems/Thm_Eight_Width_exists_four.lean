-- Prove2me | Theorems.Thm_Eight_Width_exists_four
-- name    : Eight.Width.exists_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:28.354307+00:00
-- url     : https://prove2.me/theorems/fe8d8699-1e93-4f1a-9eb3-a5feccb703a2
-- title:
--   Width: exists four
-- statement:
--   The Width construction uses the exists four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L90-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L90-L93

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

theorem Eight.Width.exists_four {C : List (V × Bool)} (h : ¬ C.length ≤ 3) : ∃ l₁ l₂ l₃ l₄ r, C = l₁ :: l₂ :: l₃ :: l₄ :: r := by sorry
