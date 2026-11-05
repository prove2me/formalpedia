-- Prove2me | Theorems.Thm_Eight_three_mul_tOf_le
-- name    : Eight.three_mul_tOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:03.591941+00:00
-- url     : https://prove2.me/theorems/fbdf169c-45a4-46bf-942b-73bac8304c99
-- title:
--   Eight: three mul t Of le
-- statement:
--   t ≤ (λ+2)/3, written without a division: 3t ≤ λ + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L78-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L78-L78

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

theorem Eight.three_mul_tOf_le (lam : ℕ) : 3 * tOf lam ≤ lam + 2 := by sorry
