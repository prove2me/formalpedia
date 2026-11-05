-- Prove2me | Theorems.Thm_Eight_change_1
-- name    : Eight.change_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:48.313566+00:00
-- url     : https://prove2.me/theorems/eecfa172-7739-4372-b26f-4153b6b0db61
-- title:
--   Eight: change 1
-- statement:
--   «and it changes d₁p₂p₃ by d₁(p₂d₃ + d₂p₃ + d₂d₃)»: d₁(p₂ + d₂)(p₃ + d₃) = d₁p₂p₃ + d₁(p₂d₃ +
--   d₂p₃ + d₂d₃).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L157-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L157-L159

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

theorem Eight.change_1 (p d : Block) : phi1 (bxor p d) d ≡ phi1 p d + chg1 p d [MOD 2] := by sorry
