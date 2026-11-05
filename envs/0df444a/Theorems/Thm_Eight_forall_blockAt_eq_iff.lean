-- Prove2me | Theorems.Thm_Eight_forall_blockAt_eq_iff
-- name    : Eight.forall_blockAt_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:04.874194+00:00
-- url     : https://prove2.me/theorems/f1eb19fc-0f72-4c9e-8b2e-f4b46a88d707
-- title:
--   Eight: forall block At eq iff
-- statement:
--   «The appended zeros agree»: two strings are equal exactly when their t blocks are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L84-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L84-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
set_option autoImplicit false
section
section
open Eight
open Finset Polynomial

theorem Eight.forall_blockAt_eq_iff {lam : ℕ} (x v : Pieces.Bits lam) : (∀ s ∈ range (tOf lam), blockAt x s = blockAt v s) ↔ x = v := by sorry
