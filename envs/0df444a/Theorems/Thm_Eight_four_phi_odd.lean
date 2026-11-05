-- Prove2me | Theorems.Thm_Eight_four_phi_odd
-- name    : Eight.four_phi_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:17.371746+00:00
-- url     : https://prove2.me/theorems/ececae58-ddc3-4774-b8be-916825e833f3
-- title:
--   Eight: four phi odd
-- statement:
--   «We have to show that φ(p,q) + φ(p ⊕ d,q ⊕ d) + φ(p,q ⊕ d) + φ(p ⊕ d,q) is odd»: the chain of
--   the congruences above.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L240-L242
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L240-L242

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

theorem Eight.four_phi_odd (p q : Block) {d : Block} (h : d ≠ (false, false, false)) :
    Odd (phi p q + phi (bxor p d) (bxor q d) + phi p (bxor q d) + phi (bxor p d) q) := by sorry
