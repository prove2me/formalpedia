-- Prove2me | Theorems.Thm_Eight_Width_splitClause_step
-- name    : Eight.Width.splitClause_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:03.266212+00:00
-- url     : https://prove2.me/theorems/f1cb1d4c-3ce7-474c-9fcd-0f4e168f3694
-- title:
--   Width: split Clause step
-- statement:
--   The Width construction uses the split Clause step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L76-L77

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

theorem Eight.Width.splitClause_step (y : V) (ys : List V) (l₁ l₂ l₃ l₄ : V × Bool) (r : List (V × Bool)) :
    splitClause (y :: ys) (l₁ :: l₂ :: l₃ :: l₄ :: r) = forced y l₁ l₂ ++ splitClause ys ((y, true) :: l₃ :: l₄ :: r) := by sorry
