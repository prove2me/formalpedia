-- Prove2me | Theorems.Thm_Eight_abs_psi_le
-- name    : Eight.abs_psi_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:47.675039+00:00
-- url     : https://prove2.me/theorems/50127dc2-31a8-49c3-a4f1-e1b6e8aadc08
-- title:
--   Eight: abs psi le
-- statement:
--   |ψ_k(p,q)| ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L141-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L141-L145

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

theorem Eight.abs_psi_le (k p q : Block) : |psi k p q| ≤ 1 := by sorry
