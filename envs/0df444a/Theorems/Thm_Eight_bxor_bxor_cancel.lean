-- Prove2me | Theorems.Thm_Eight_bxor_bxor_cancel
-- name    : Eight.bxor_bxor_cancel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:28.800114+00:00
-- url     : https://prove2.me/theorems/919c6f5c-57e7-4306-abc9-f5eb79769fe6
-- title:
--   Eight: bxor bxor cancel
-- statement:
--   (p ⊕ d) ⊕ d = p.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L56-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L56-L56

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

theorem Eight.bxor_bxor_cancel (p d : Block) : bxor (bxor p d) d = p := by sorry
