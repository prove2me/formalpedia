-- Prove2me | Theorems.Thm_Eight_colNetwork_sized_t
-- name    : Eight.colNetwork_sized_t
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:06:37.379554+00:00
-- url     : https://prove2.me/theorems/c2b2c362-611d-499e-af49-f42df429c8ce
-- title:
--   Eight: col Network sized t
-- statement:
--   The same for the column network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L132-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L132-L139

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

theorem Eight.colNetwork_sized_t {B : ℕ} (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) (hW : ∀ w h, |W w h| ≤ 2 ^ B) {ι : Rectangle g → ℕ}
    (hι : ∀ q, ι q ≤ tOf lam) : (colNetwork W ι).Sized (g ^ 3 * lam) (g * B + g ^ 2 * tOf lam) := by sorry
