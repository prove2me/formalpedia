-- Prove2me | Theorems.Thm_Eight_Width_nodup_freshFin
-- name    : Eight.Width.nodup_freshFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:47:32.421568+00:00
-- url     : https://prove2.me/theorems/9004efb3-a669-49b2-9cbd-0f0e099312be
-- title:
--   Width: nodup fresh Fin
-- statement:
--   The Width construction uses the nodup fresh Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L339-L340
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L339-L340

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

theorem Eight.Width.nodup_freshFin (n N : ℕ) : (freshFin n N).Nodup := by sorry
