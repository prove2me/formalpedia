-- Prove2me | Theorems.Thm_Eight_phiQ_self
-- name    : Eight.phiQ_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:06.694084+00:00
-- url     : https://prove2.me/theorems/7d019690-6753-4ff4-806e-2daccf6624a4
-- title:
--   Eight: phi Q self
-- statement:
--   «With d_i² = d_i», for the first change: Σ_{1 ≤ i ≤ j ≤ 3} d_i d_j = d₁ + d₂ + d₃ + d₁d₂ + d₁d₃ +
--   d₂d₃.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L192-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L192-L196

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

theorem Eight.phiQ_self (d : Block) : phiQ d d
    = d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat := by sorry
