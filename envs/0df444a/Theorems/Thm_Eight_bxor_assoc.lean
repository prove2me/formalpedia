-- Prove2me | Theorems.Thm_Eight_bxor_assoc
-- name    : Eight.bxor_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:12.858562+00:00
-- url     : https://prove2.me/theorems/3ceda44f-8528-44c3-b6ad-81ec1b7d2080
-- title:
--   Eight: bxor assoc
-- statement:
--   (p ⊕ q) ⊕ r = p ⊕ (q ⊕ r): the same law in each bit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L47-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L47-L47

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

theorem Eight.bxor_assoc (p q r : Block) : bxor (bxor p q) r = bxor p (bxor q r) := by sorry
