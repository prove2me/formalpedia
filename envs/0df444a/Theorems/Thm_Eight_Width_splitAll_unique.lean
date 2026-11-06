-- Prove2me | Theorems.Thm_Eight_Width_splitAll_unique
-- name    : Eight.Width.splitAll_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:46:49.606584+00:00
-- url     : https://prove2.me/theorems/31515eb4-3481-40a0-82cf-72e8d4ab06fa
-- title:
--   Width: split All unique
-- statement:
--   Two assignments that satisfy the image and agree on the variables of the formula agree on the
--   fresh variables, if all of these are used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L271-L282
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L271-L282

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

theorem Eight.Width.splitAll_unique (b b' : V → Bool) : ∀ (φ : List (List (V × Bool))) (ys : List V), ys.length ≤ numFresh φ →
    (∀ C ∈ φ, ∀ l ∈ C, b l.1 = b' l.1) → Holds b (splitAll ys φ) → Holds b' (splitAll ys φ) → ∀ y ∈ ys, b y = b' y
  := by sorry
