-- Prove2me | Theorems.Thm_Eight_four_phi
-- name    : Eight.four_phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:43.188551+00:00
-- url     : https://prove2.me/theorems/e4acbc0b-0f03-46bc-8aef-52b45ee968e3
-- title:
--   Eight: four phi
-- statement:
--   «and the sum is φ(p,d) + φ(p ⊕ d,d)»: the line before, used for p and for p ⊕ d.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L118-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L118-L123

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

theorem Eight.four_phi (p q d : Block) :
    phi p q + phi (bxor p d) (bxor q d) + phi p (bxor q d) + phi (bxor p d) q ≡ phi p d + phi (bxor p d) d [MOD 2] := by sorry
