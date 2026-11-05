-- Prove2me | Theorems.Thm_Eight_four_changes
-- name    : Eight.four_changes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:10.981872+00:00
-- url     : https://prove2.me/theorems/03ae753f-7590-497e-b235-5c71a5575df7
-- title:
--   Eight: four changes
-- statement:
--   «in which the terms that occur twice cancel. With d_i² = d_i this is d₁ + d₂ + d₃ + d₁d₂ + d₁d₃ +
--   d₂d₃ + d₁d₂d₃».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L200-L206
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L200-L206

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

theorem Eight.four_changes (p d : Block) : phiQ d d + chg1 p d + chg2 p d + chg3 p d
    ≡ d.1.toNat + d.2.1.toNat + d.2.2.toNat + d.1.toNat * d.2.1.toNat + d.1.toNat * d.2.2.toNat + d.2.1.toNat * d.2.2.toNat
      + d.1.toNat * d.2.1.toNat * d.2.2.toNat [MOD 2] := by sorry
