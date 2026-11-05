-- Prove2me | Theorems.Thm_Eight_d_eq
-- name    : Eight.d_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:28.020355+00:00
-- url     : https://prove2.me/theorems/24509e0d-d129-4107-9ee0-6a0677e8e8d8
-- title:
--   Eight: d eq
-- statement:
--   «and it equals p ⊕ p' because p ⊕ q = p' ⊕ q'»: q ⊕ q' = p ⊕ (p ⊕ q) ⊕ q' = p ⊕ (p' ⊕ q') ⊕ q' =
--   p ⊕ p'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L70-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L70-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.d_eq {p q p' q' : Block} (h : bxor p q = bxor p' q') : bxor q q' = bxor p p' := by sorry
