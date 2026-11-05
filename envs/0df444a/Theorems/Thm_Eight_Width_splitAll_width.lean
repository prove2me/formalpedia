-- Prove2me | Theorems.Thm_Eight_Width_splitAll_width
-- name    : Eight.Width.splitAll_width
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:47:01.957568+00:00
-- url     : https://prove2.me/theorems/0f78e341-2171-4289-a81e-02466089912a
-- title:
--   Width: split All width
-- statement:
--   With enough fresh variables every clause of the image has at most 3 literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L285-L293
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L285-L293

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

theorem Eight.Width.splitAll_width : ∀ (φ : List (List (V × Bool))) (ys : List V), numFresh φ ≤ ys.length →
    ∀ D ∈ splitAll ys φ, D.length ≤ 3
  := by sorry
