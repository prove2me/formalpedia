-- Prove2me | Theorems.Thm_Eight_Width_widthReduce_eq
-- name    : Eight.Width.widthReduce_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:47:00.173683+00:00
-- url     : https://prove2.me/theorems/8011e3b1-9f1b-4cd4-bca0-683809b86905
-- title:
--   Width: width Reduce eq
-- statement:
--   The Width construction uses the width Reduce eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L326-L326
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L326-L326

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
variable {n : ℕ}

theorem Eight.Width.widthReduce_eq (φ : CNF n) : widthReduce φ = (splitAll (freshFin n (numFresh φ)) (lift (numFresh φ) φ)).dedup := by sorry
