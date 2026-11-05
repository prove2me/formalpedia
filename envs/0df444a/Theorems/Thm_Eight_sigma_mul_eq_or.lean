-- Prove2me | Theorems.Thm_Eight_sigma_mul_eq_or
-- name    : Eight.sigma_mul_eq_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:20.839208+00:00
-- url     : https://prove2.me/theorems/fa80e54e-9cb6-49df-85dd-7bf226841669
-- title:
--   Eight: sigma mul eq or
-- statement:
--   A product of two signs is 1 or −1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L36-L37

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

theorem Eight.sigma_mul_eq_or (p q p' q' : Block) : sigma p q * sigma p' q' = 1 ∨ sigma p q * sigma p' q' = -1 := by sorry
