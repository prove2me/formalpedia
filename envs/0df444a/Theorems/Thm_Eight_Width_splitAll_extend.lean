-- Prove2me | Theorems.Thm_Eight_Width_splitAll_extend
-- name    : Eight.Width.splitAll_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:46:50.930506+00:00
-- url     : https://prove2.me/theorems/b617f23e-2bd8-44cd-85b8-9f783b4db1fe
-- title:
--   Width: split All extend
-- statement:
--   An assignment that satisfies the formula can be changed on the fresh variables so that it
--   satisfies the image.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L248-L267
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L248-L267

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

theorem Eight.Width.splitAll_extend : ∀ (φ : List (List (V × Bool))) (ys : List V) (a : V → Bool), ys.Nodup →
    (∀ C ∈ φ, ∀ l ∈ C, l.1 ∉ ys) → Holds a φ → ∃ b : V → Bool, (∀ v, v ∉ ys → b v = a v) ∧ Holds b (splitAll ys φ)
  := by sorry
