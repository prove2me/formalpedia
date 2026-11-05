-- Prove2me | Theorems.Thm_Eight_Width_holds_dedup
-- name    : Eight.Width.holds_dedup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:47.149593+00:00
-- url     : https://prove2.me/theorems/a10882bd-556d-429d-b009-707737012895
-- title:
--   Width: holds dedup
-- statement:
--   The Width construction uses the holds dedup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L328-L329
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/Width.lean#L328-L329

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

theorem Eight.Width.holds_dedup {W : Type} [DecidableEq W] {a : W → Bool} {φ : List (List (W × Bool))} : Holds a φ.dedup ↔ Holds a φ := by sorry
