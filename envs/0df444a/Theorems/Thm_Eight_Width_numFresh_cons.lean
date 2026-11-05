-- Prove2me | Theorems.Thm_Eight_Width_numFresh_cons
-- name    : Eight.Width.numFresh_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:40.675075+00:00
-- url     : https://prove2.me/theorems/76d99929-27e4-490b-8135-ba5994df354b
-- title:
--   Width: num Fresh cons
-- statement:
--   The Width construction uses the num Fresh cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L235-L236
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L235-L236

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

theorem Eight.Width.numFresh_cons (C : List (V × Bool)) (φ : List (List (V × Bool))) :
    numFresh (C :: φ) = (C.length - 3) + numFresh φ := by sorry
