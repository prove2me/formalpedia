-- Prove2me | Theorems.Thm_Eight_phi_linear
-- name    : Eight.phi_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:31.298849+00:00
-- url     : https://prove2.me/theorems/01c20105-1551-4253-9da5-77b92bead207
-- title:
--   Eight: phi linear
-- statement:
--   «Every term of φ(p,q) contains exactly one bit of q»: collected by that bit, φ(p,q) = (p₁ +
--   p₂p₃)·q₁ + (p₁ + p₂ + p₁p₃)·q₂ + (p₁ + p₂ + p₃ + p₁p₂)·q₃.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L96-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L96-L97

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

theorem Eight.phi_linear (p q : Block) : phi p q = lin1 p * q.1.toNat + lin2 p * q.2.1.toNat + lin3 p * q.2.2.toNat := by sorry
