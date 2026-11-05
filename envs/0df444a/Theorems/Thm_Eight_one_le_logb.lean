-- Prove2me | Theorems.Thm_Eight_one_le_logb
-- name    : Eight.one_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:48:55.546097+00:00
-- url     : https://prove2.me/theorems/d6c713e9-0f9e-4d7d-bf71-6d7e6775c6fb
-- title:
--   Eight: one le logb
-- statement:
--   log₂(2λ) ≥ 1 for λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/App_Pieces.lean#L42-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_App_Pieces
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.one_le_logb {lam : ℕ} (hl : 1 ≤ lam) : (1 : ℝ) ≤ Real.logb 2 (2 * lam) := by sorry
