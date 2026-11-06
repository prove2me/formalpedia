-- Prove2me | Theorems.Thm_Eight_Width_natAdd_mem_freshFin
-- name    : Eight.Width.natAdd_mem_freshFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:47:40.166356+00:00
-- url     : https://prove2.me/theorems/9c3c7041-0a91-4c4f-973b-558c98c9df31
-- title:
--   Width: nat Add mem fresh Fin
-- statement:
--   The Width construction uses the nat Add mem fresh Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L342-L342
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L342-L342

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

theorem Eight.Width.natAdd_mem_freshFin (n N : ℕ) (j : Fin N) : Fin.natAdd n j ∈ freshFin n N := by sorry
