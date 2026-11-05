-- Prove2me | Theorems.Thm_Eight_bxor_bit3
-- name    : Eight.bxor_bit3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:20.206769+00:00
-- url     : https://prove2.me/theorems/73939f3e-4f8c-4e13-921a-ef18e7f1c0c7
-- title:
--   Eight: bxor bit3
-- statement:
--   The Eight construction uses the bxor bit3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L41-L41

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

theorem Eight.bxor_bit3 (p q : Block) : (bxor p q).2.2 = (p.2.2 ^^ q.2.2) := by sorry
