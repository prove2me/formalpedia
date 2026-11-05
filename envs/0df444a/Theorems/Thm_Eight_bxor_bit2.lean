-- Prove2me | Theorems.Thm_Eight_bxor_bit2
-- name    : Eight.bxor_bit2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:15.739195+00:00
-- url     : https://prove2.me/theorems/40f65b3f-2d84-481c-addc-f1ec762ddea1
-- title:
--   Eight: bxor bit2
-- statement:
--   The Eight construction uses the bxor bit2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L40-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L40-L40

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

theorem Eight.bxor_bit2 (p q : Block) : (bxor p q).2.1 = (p.2.1 ^^ q.2.1) := by sorry
