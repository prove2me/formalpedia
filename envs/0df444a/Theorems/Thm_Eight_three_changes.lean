-- Prove2me | Theorems.Thm_Eight_three_changes
-- name    : Eight.three_changes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:50.803845+00:00
-- url     : https://prove2.me/theorems/3a731b50-7f3b-441a-91b1-5566c97a8e04
-- title:
--   Eight: three changes
-- statement:
--   «In these three changes each of p₁d₂d₃, p₂d₁d₃, p₃d₁d₂ occurs twice and d₁d₂d₃ three times».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L172-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L172-L175

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

theorem Eight.three_changes (p d : Block) : chg1 p d + chg2 p d + chg3 p d
    = 2 * (p.1.toNat * d.2.1.toNat * d.2.2.toNat + p.2.1.toNat * d.1.toNat * d.2.2.toNat + p.2.2.toNat * d.1.toNat * d.2.1.toNat)
      + 3 * (d.1.toNat * d.2.1.toNat * d.2.2.toNat) := by sorry
