-- Prove2me | Theorems.Thm_Eight_one_add_prod
-- name    : Eight.one_add_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:13.220737+00:00
-- url     : https://prove2.me/theorems/8c64328b-7351-41ab-a8f3-8370d6e4eef3
-- title:
--   Eight: one add prod
-- statement:
--   «which is 1 because some d_i is 1»: the factor 1 + d_i is then 2, so the product is even.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L226-L236
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L226-L236

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

theorem Eight.one_add_prod {d : Block} (h : d ≠ (false, false, false)) :
    1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) ≡ 1 [MOD 2] := by sorry
