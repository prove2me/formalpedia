-- Prove2me | Theorems.Thm_Eight_two_pow_tOf_lt
-- name    : Eight.two_pow_tOf_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:48:50.849669+00:00
-- url     : https://prove2.me/theorems/c7faabef-0fa1-43c4-84a5-9b502ffa9ec3
-- title:
--   Eight: two pow t Of lt
-- statement:
--   2^t < 2^((2λ)^c).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L36-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L36-L39

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

theorem Eight.two_pow_tOf_lt {lam c : ℕ} (hl : 1 ≤ lam) (hc : 1 ≤ c) : (2 : ℤ) ^ tOf lam < 2 ^ (2 * lam) ^ c := by sorry
