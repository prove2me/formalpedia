-- Prove2me | Theorems.Thm_Eight_two_mul_le_pow
-- name    : Eight.two_mul_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:23.219279+00:00
-- url     : https://prove2.me/theorems/4103e6ac-3903-4053-9750-dc22a7b14c51
-- title:
--   Eight: two mul le pow
-- statement:
--   2λ ≤ (2λ)^c for c ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_App_Pieces
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.two_mul_le_pow (lam : ℕ) {c : ℕ} (hc : 1 ≤ c) : 2 * lam ≤ (2 * lam) ^ c := by sorry
