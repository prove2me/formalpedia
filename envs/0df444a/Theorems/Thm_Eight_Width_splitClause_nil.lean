-- Prove2me | Theorems.Thm_Eight_Width_splitClause_nil
-- name    : Eight.Width.splitClause_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:32.171142+00:00
-- url     : https://prove2.me/theorems/9a3c3e6d-9a83-4654-859b-73cc6257fcc9
-- title:
--   Width: split Clause nil
-- statement:
--   The Width construction uses the split Clause nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L79-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L79-L79

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

theorem Eight.Width.splitClause_nil (C : List (V × Bool)) : splitClause [] C = [C] := by sorry
