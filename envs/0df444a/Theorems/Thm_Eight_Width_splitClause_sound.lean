-- Prove2me | Theorems.Thm_Eight_Width_splitClause_sound
-- name    : Eight.Width.splitClause_sound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:46:08.509414+00:00
-- url     : https://prove2.me/theorems/cdecdca5-f24b-437e-883a-ff7bd6919536
-- title:
--   Width: split Clause sound
-- statement:
--   An assignment that satisfies the clauses made from C satisfies C. (No condition on the variables
--   ys.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L97-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L97-L113

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

theorem Eight.Width.splitClause_sound (a : V → Bool) : ∀ (ys : List V) (C : List (V × Bool)),
    Holds a (splitClause ys C) → ∃ l ∈ C, a l.1 = l.2
  := by sorry
