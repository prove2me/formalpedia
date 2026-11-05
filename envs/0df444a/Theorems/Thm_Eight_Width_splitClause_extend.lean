-- Prove2me | Theorems.Thm_Eight_Width_splitClause_extend
-- name    : Eight.Width.splitClause_extend
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:46:25.580124+00:00
-- url     : https://prove2.me/theorems/29a7119f-cb1a-4010-814b-91654a6b1ee5
-- title:
--   Width: split Clause extend
-- statement:
--   An assignment that satisfies C can be changed on the fresh variables ys so that it satisfies the
--   clauses made from C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L141-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L141-L178

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

theorem Eight.Width.splitClause_extend : ∀ (ys : List V) (C : List (V × Bool)) (a : V → Bool), ys.Nodup → (∀ l ∈ C, l.1 ∉ ys) →
    (∃ l ∈ C, a l.1 = l.2) → ∃ b : V → Bool, (∀ v, v ∉ ys → b v = a v) ∧ Holds b (splitClause ys C)
  := by sorry
