-- Prove2me | Theorems.Thm_Eight_rowCut_factors
-- name    : Eight.rowCut_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:31:21.402078+00:00
-- url     : https://prove2.me/theorems/4b1ae380-9118-4142-b41d-ada0d97ee732
-- title:
--   Eight: row Cut factors
-- statement:
--   Lemma 2(b), first factorization.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L75-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L75-L77

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

theorem Eight.rowCut_factors (hlam : 1 ≤ lam) {i : ℕ} (hi : i ≤ tOf lam) : (rowCut lam i).Factors (Eight.A lam i) := by sorry
