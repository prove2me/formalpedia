-- Prove2me | Theorems.Thm_Eight_change_3
-- name    : Eight.change_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:51.69884+00:00
-- url     : https://prove2.me/theorems/7af326b8-25fc-4eb0-995c-5a742804f661
-- title:
--   Eight: change 3
-- statement:
--   «and p₁p₂d₃ by d₃(p₁d₂ + d₁p₂ + d₁d₂)»: (p₁ + d₁)(p₂ + d₂)d₃ = p₁p₂d₃ + d₃(p₁d₂ + d₁p₂ + d₁d₂).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L167-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L167-L169

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

theorem Eight.change_3 (p d : Block) : phi3 (bxor p d) d ≡ phi3 p d + chg3 p d [MOD 2] := by sorry
