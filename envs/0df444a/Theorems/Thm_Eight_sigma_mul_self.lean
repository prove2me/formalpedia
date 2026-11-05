-- Prove2me | Theorems.Thm_Eight_sigma_mul_self
-- name    : Eight.sigma_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:17.973765+00:00
-- url     : https://prove2.me/theorems/fd7c9ace-59ac-4f04-b121-0d544b54a1de
-- title:
--   Eight: sigma mul self
-- statement:
--   σ(p,q)² = 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.sigma_mul_self (p q : Block) : sigma p q * sigma p q = 1 := by sorry
