-- Prove2me | Theorems.Thm_Eight_block_ext
-- name    : Eight.block_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:32.643691+00:00
-- url     : https://prove2.me/theorems/14ff8e27-1854-4920-8e91-af9e09e9ed7c
-- title:
--   Eight: block ext
-- statement:
--   Two blocks with the same three bits are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L36-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L36-L36

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

theorem Eight.block_ext {p q : Block} (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1) (h3 : p.2.2 = q.2.2) : p = q := by sorry
