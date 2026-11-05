-- Prove2me | Theorems.Thm_Eight_phi_add_phi_shift
-- name    : Eight.phi_add_phi_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:59.90169+00:00
-- url     : https://prove2.me/theorems/c2a4a4aa-484c-4c39-9a68-0086f8c82658
-- title:
--   Eight: phi add phi shift
-- statement:
--   «So φ(p,d) + φ(p ⊕ d,d) is congruent to the sum of the four changes».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L178-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L178-L185

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

theorem Eight.phi_add_phi_shift (p d : Block) : phi p d + phi (bxor p d) d ≡ phiQ d d + chg1 p d + chg2 p d + chg3 p d [MOD 2] := by sorry
