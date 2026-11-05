-- Prove2me | Theorems.Thm_Eight_Width_length_splitClause
-- name    : Eight.Width.length_splitClause
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:46:40.104007+00:00
-- url     : https://prove2.me/theorems/b1d62cb8-08f1-40fa-ada1-d07f10749957
-- title:
--   Width: length split Clause
-- statement:
--   The number of clauses made from C: 1, and 3 for each fresh variable that is used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L220-L228
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L220-L228

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

theorem Eight.Width.length_splitClause : ∀ (ys : List V) (C : List (V × Bool)),
    (splitClause ys C).length = 1 + 3 * min ys.length (C.length - 3)
  := by sorry
