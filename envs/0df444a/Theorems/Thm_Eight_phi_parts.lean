-- Prove2me | Theorems.Thm_Eight_phi_parts
-- name    : Eight.phi_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:50.761998+00:00
-- url     : https://prove2.me/theorems/2dca9049-3f98-402e-8552-57f3cc0fa0cc
-- title:
--   Eight: phi parts
-- statement:
--   φ is the sum of its four parts (by definition).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L136-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L136-L136

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

theorem Eight.phi_parts (p q : Block) : phi p q = phiQ p q + phi1 p q + phi2 p q + phi3 p q := by sorry
