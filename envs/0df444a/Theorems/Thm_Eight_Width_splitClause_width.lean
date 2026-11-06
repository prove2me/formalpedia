-- Prove2me | Theorems.Thm_Eight_Width_splitClause_width
-- name    : Eight.Width.splitClause_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:46:30.063202+00:00
-- url     : https://prove2.me/theorems/29bc72a6-3cbd-4f1c-bf72-5526e0113166
-- title:
--   Width: split Clause width
-- statement:
--   With enough fresh variables every clause made from C has at most 3 literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L202-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L202-L217

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

theorem Eight.Width.splitClause_width : ∀ (ys : List V) (C : List (V × Bool)), C.length - 3 ≤ ys.length →
    ∀ D ∈ splitClause ys C, D.length ≤ 3
  := by sorry
