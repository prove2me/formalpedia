-- Prove2me | Theorems.Thm_Eight_exists_bit
-- name    : Eight.exists_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:05.185673+00:00
-- url     : https://prove2.me/theorems/0011b14f-1889-486c-bda9-c80bf0095ba6
-- title:
--   Eight: exists bit
-- statement:
--   «some d_i is 1», since d is not 000.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L220-L223
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L220-L223

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

theorem Eight.exists_bit {d : Block} (h : d ≠ (false, false, false)) : d.1 = true ∨ d.2.1 = true ∨ d.2.2 = true := by sorry
