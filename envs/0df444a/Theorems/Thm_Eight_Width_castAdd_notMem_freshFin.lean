-- Prove2me | Theorems.Thm_Eight_Width_castAdd_notMem_freshFin
-- name    : Eight.Width.castAdd_notMem_freshFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:10:17.222556+00:00
-- url     : https://prove2.me/theorems/fd542fc3-eae3-422d-81a6-194fb14e7ac7
-- title:
--   Width: cast Add not Mem fresh Fin
-- statement:
--   The Width construction uses the cast Add not Mem fresh Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L344-L349
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L344-L349

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

theorem Eight.Width.castAdd_notMem_freshFin (n N : ℕ) (i : Fin n) : Fin.castAdd N i ∉ freshFin n N := by sorry
