-- Prove2me | Theorems.Thm_Eight_change_Q
-- name    : Eight.change_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:49.055774+00:00
-- url     : https://prove2.me/theorems/6f5261a7-b913-4032-a5b0-a69fe36f8ccc
-- title:
--   Eight: change Q
-- statement:
--   «Replacing p by p ⊕ d changes Σ_{1 ≤ i ≤ j ≤ 3} p_i d_j by Σ_{1 ≤ i ≤ j ≤ 3} d_i d_j» (modulo 2).
--   In this and the next three: put p_i + d_i for each bit of p ⊕ d (toNat_xor) and multiply out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L146-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L146-L153

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

theorem Eight.change_Q (p d : Block) : phiQ (bxor p d) d ≡ phiQ p d + phiQ d d [MOD 2] := by sorry
