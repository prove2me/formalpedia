-- Prove2me | Theorems.Thm_Eight_Width_length_splitAll
-- name    : Eight.Width.length_splitAll
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:47:04.935219+00:00
-- url     : https://prove2.me/theorems/1274a828-4bed-4294-8309-c2b4b53c54ea
-- title:
--   Width: length split All
-- statement:
--   With enough fresh variables the image, before repetitions are struck out, has exactly m + 3N
--   clauses: m the number of clauses of the formula, N the number of fresh variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L297-L303
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L297-L303

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

theorem Eight.Width.length_splitAll : ∀ (φ : List (List (V × Bool))) (ys : List V), numFresh φ ≤ ys.length →
    (splitAll ys φ).length = φ.length + 3 * numFresh φ
  := by sorry
