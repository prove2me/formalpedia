-- Prove2me | Theorems.Thm_Eight_sum_A_eq_prod
-- name    : Eight.sum_A_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:15.757942+00:00
-- url     : https://prove2.me/theorems/299b99ab-ca47-4ca0-817e-d55698654486
-- title:
--   Eight: sum A eq prod
-- statement:
--   «Set T = 1»: A_0 + … + A_t is the value of the product at T = 1, which is ∏_s (R + C).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L113-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L113-L119

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

theorem Eight.sum_A_eq_prod {lam : ℕ} (x y u v : Pieces.Bits lam) :
    ∑ i ∈ range (tOf lam + 1), A lam i x y u v =
      ∏ s ∈ range (tOf lam), (Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) + Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s)) := by sorry
