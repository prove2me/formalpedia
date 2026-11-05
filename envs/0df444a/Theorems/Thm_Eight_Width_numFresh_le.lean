-- Prove2me | Theorems.Thm_Eight_Width_numFresh_le
-- name    : Eight.Width.numFresh_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:58.380227+00:00
-- url     : https://prove2.me/theorems/ed300b9d-b4bd-446b-8eb4-591207cd922b
-- title:
--   Width: num Fresh le
-- statement:
--   At most k − 3 fresh variables for each clause of a k-CNF.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L306-L312
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L306-L312

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

theorem Eight.Width.numFresh_le (k : ℕ) : ∀ φ : List (List (V × Bool)), (∀ C ∈ φ, C.length ≤ k) → numFresh φ ≤ (k - 3) * φ.length
  := by sorry
