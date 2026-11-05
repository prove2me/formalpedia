-- Prove2me | Theorems.Thm_Eight_bitAt_of_lt
-- name    : Eight.bitAt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:00.647463+00:00
-- url     : https://prove2.me/theorems/01ef4659-f7bc-412e-82cf-42ac9c4b4d77
-- title:
--   Eight: bit At of lt
-- statement:
--   A bit of the string itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L81-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L81-L81

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

theorem Eight.bitAt_of_lt {lam : ℕ} (x : Pieces.Bits lam) (j : Fin lam) : bitAt x j = x j := by sorry
