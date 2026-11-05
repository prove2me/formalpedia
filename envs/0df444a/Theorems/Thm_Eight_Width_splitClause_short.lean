-- Prove2me | Theorems.Thm_Eight_Width_splitClause_short
-- name    : Eight.Width.splitClause_short
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:41.881605+00:00
-- url     : https://prove2.me/theorems/a614d82f-9e92-47c6-8463-190a7389f6ff
-- title:
--   Width: split Clause short
-- statement:
--   The Width construction uses the split Clause short property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L81-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L81-L88

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

theorem Eight.Width.splitClause_short (ys : List V) {C : List (V × Bool)} (h : C.length ≤ 3) : splitClause ys C = [C] := by sorry
