-- Prove2me | Theorems.Thm_Eight_crow_add_ccol_le
-- name    : Eight.crow_add_ccol_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:02.401291+00:00
-- url     : https://prove2.me/theorems/227bd308-c394-43bb-804d-36540701c5a6
-- title:
--   Eight: crow add ccol le
-- statement:
--   «c_i^row + c_i^col ≤ (4t + 3i) + (7t − 3i) = 11t», for i ≤ t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L161-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L161-L164

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
set_option autoImplicit false
section
section
open Eight
open Finset Polynomial

theorem Eight.crow_add_ccol_le {lam i : ℕ} (hi : i ≤ tOf lam) : crow lam i + ccol lam i ≤ 11 * tOf lam := by sorry
