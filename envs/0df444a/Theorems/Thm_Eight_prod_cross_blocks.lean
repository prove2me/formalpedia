-- Prove2me | Theorems.Thm_Eight_prod_cross_blocks
-- name    : Eight.prod_cross_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:08.575272+00:00
-- url     : https://prove2.me/theorems/fc12a65d-3348-42cf-8cb9-53f22fcd09d3
-- title:
--   Eight: prod cross blocks
-- statement:
--   ∏_s [x_s = v_s][y_s = u_s] = [x = v][y = u].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L103-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L103-L108

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

theorem Eight.prod_cross_blocks {lam : ℕ} (x y u v : Pieces.Bits lam) :
    ∏ s ∈ range (tOf lam), (if blockAt x s = blockAt v s ∧ blockAt y s = blockAt u s then (1 : ℤ) else 0) = Pieces.cross x y u v := by sorry
