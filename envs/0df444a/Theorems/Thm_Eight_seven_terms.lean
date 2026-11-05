-- Prove2me | Theorems.Thm_Eight_seven_terms
-- name    : Eight.seven_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:05.885183+00:00
-- url     : https://prove2.me/theorems/1b279d95-9076-4428-a222-7f32a1485912
-- title:
--   Eight: seven terms
-- statement:
--   «≡ 1 + (1 + d₁)(1 + d₂)(1 + d₃)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L209-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L209-L217

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

theorem Eight.seven_terms (d : Block) :
    d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
      + d.1.toNat * d.2.1.toNat * d.2.2.toNat ≡ 1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) [MOD 2] := by sorry
