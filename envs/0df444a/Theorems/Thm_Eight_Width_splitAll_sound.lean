-- Prove2me | Theorems.Thm_Eight_Width_splitAll_sound
-- name    : Eight.Width.splitAll_sound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:46:42.88858+00:00
-- url     : https://prove2.me/theorems/24bfa832-e2cf-48bb-84cc-daea220f8f02
-- title:
--   Width: split All sound
-- statement:
--   An assignment that satisfies the image satisfies the formula. (No condition on the variables
--   ys.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L240-L244
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L240-L244

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

theorem Eight.Width.splitAll_sound (a : V → Bool) : ∀ (φ : List (List (V × Bool))) (ys : List V), Holds a (splitAll ys φ) → Holds a φ
  := by sorry
