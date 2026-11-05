-- Prove2me | Theorems.Thm_Eight_bxor_eq_iff_zero
-- name    : Eight.bxor_eq_iff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:20.788244+00:00
-- url     : https://prove2.me/theorems/07bbf557-ac3e-4eac-b5d0-c84d6b5488bd
-- title:
--   Eight: bxor eq iff zero
-- statement:
--   «Both brackets say x ⊕ y ⊕ u ⊕ v = 000»: x ⊕ y = v ⊕ u says this.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L40-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L40-L43

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

theorem Eight.bxor_eq_iff_zero (x y u v : Block) : bxor x y = bxor v u ↔ bxor (bxor x y) (bxor u v) = (false, false, false) := by sorry
