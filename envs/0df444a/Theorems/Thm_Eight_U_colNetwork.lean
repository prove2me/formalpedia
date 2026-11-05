-- Prove2me | Theorems.Thm_Eight_U_colNetwork
-- name    : Eight.U_colNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:06:37.578551+00:00
-- url     : https://prove2.me/theorems/faefd12c-b8fd-4aed-bea3-8b50739d8d4b
-- title:
--   Eight: U col Network
-- statement:
--   «U_col = g²(g−1)λ + 2 ∑_{q ∈ ℛ} c^col_{ι(q)}». Same as in the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L150-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L150-L153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Paper_card_rectangles
import Theorems.Thm_Paper_card_rectangles_le
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
open Eight
open Finset Groundwork
open Paper (Rectangle rectangles mem_rectangles card_rectangles card_rectangles_le Settings RowSetting FactorsThrough)
variable {g lam : ℕ}

theorem Eight.U_colNetwork (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    (colNetwork W ι).U = g ^ 2 * (g - 1) * lam + 2 * ∑ q ∈ rectangles g, ccol lam (ι q) := by sorry
