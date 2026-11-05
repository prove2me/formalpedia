-- Prove2me | Theorems.Thm_Eight_change_2
-- name    : Eight.change_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:50.433206+00:00
-- url     : https://prove2.me/theorems/a9a48921-9509-400f-9bc5-7d33ef1a009e
-- title:
--   Eight: change 2
-- statement:
--   «p₁d₂p₃ by d₂(p₁d₃ + d₁p₃ + d₁d₃)»: (p₁ + d₁)d₂(p₃ + d₃) = p₁d₂p₃ + d₂(p₁d₃ + d₁p₃ + d₁d₃).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L162-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L162-L164

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

theorem Eight.change_2 (p d : Block) : phi2 (bxor p d) d ≡ phi2 p d + chg2 p d [MOD 2] := by sorry
