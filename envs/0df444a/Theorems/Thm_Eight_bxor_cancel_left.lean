-- Prove2me | Theorems.Thm_Eight_bxor_cancel_left
-- name    : Eight.bxor_cancel_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:43.800468+00:00
-- url     : https://prove2.me/theorems/59f7abe4-da80-4bf0-a5e0-88d37fa0f07a
-- title:
--   Eight: bxor cancel left
-- statement:
--   p ⊕ (p ⊕ q) = q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L59-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L59-L59

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

theorem Eight.bxor_cancel_left (p q : Block) : bxor p (bxor p q) = q := by sorry
