-- Prove2me | Theorems.Thm_Eight_Width_splitClause_unique
-- name    : Eight.Width.splitClause_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:46:32.600205+00:00
-- url     : https://prove2.me/theorems/0bb7e9e0-c570-4088-83b2-e7e8165672aa
-- title:
--   Width: split Clause unique
-- statement:
--   Two assignments that satisfy the clauses made from C and agree on the variables of C agree on
--   the fresh variables, if all of these are used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L182-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L182-L199

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

theorem Eight.Width.splitClause_unique (b b' : V → Bool) : ∀ (ys : List V) (C : List (V × Bool)), ys.length ≤ C.length - 3 →
    (∀ l ∈ C, b l.1 = b' l.1) → Holds b (splitClause ys C) → Holds b' (splitClause ys C) → ∀ y ∈ ys, b y = b' y
  := by sorry
