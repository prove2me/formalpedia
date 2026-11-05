-- Prove2me | Theorems.Thm_Eight_Width_splitClause_vars
-- name    : Eight.Width.splitClause_vars
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:46:09.312717+00:00
-- url     : https://prove2.me/theorems/bc77a7cd-6736-4a07-856c-1fe00bf6f72c
-- title:
--   Width: split Clause vars
-- statement:
--   A variable of a clause made from C is one of ys or a variable of C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L116-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L116-L137

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

theorem Eight.Width.splitClause_vars : ∀ (ys : List V) (C : List (V × Bool)), ∀ D ∈ splitClause ys C, ∀ l ∈ D,
    l.1 ∈ ys ∨ ∃ l' ∈ C, l'.1 = l.1
  := by sorry
