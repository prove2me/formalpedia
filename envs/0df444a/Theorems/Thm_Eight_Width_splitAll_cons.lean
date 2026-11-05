-- Prove2me | Theorems.Thm_Eight_Width_splitAll_cons
-- name    : Eight.Width.splitAll_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:32.124463+00:00
-- url     : https://prove2.me/theorems/b8a1ee74-a219-4340-964d-2109b1a2d416
-- title:
--   Width: split All cons
-- statement:
--   The Width construction uses the split All cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L232-L233
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L232-L233

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

theorem Eight.Width.splitAll_cons (ys : List V) (C : List (V × Bool)) (φ : List (List (V × Bool))) :
    splitAll ys (C :: φ) = splitClause (ys.take (C.length - 3)) C ++ splitAll (ys.drop (C.length - 3)) φ := by sorry
