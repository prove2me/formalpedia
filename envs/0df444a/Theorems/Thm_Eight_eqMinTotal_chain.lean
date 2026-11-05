-- Prove2me | Theorems.Thm_Eight_eqMinTotal_chain
-- name    : Eight.eqMinTotal_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:06:48.467294+00:00
-- url     : https://prove2.me/theorems/f3b97473-1990-48c6-b20f-151808db9e55
-- title:
--   Eight: eq Min Total chain
-- statement:
--   **Display (36) of the paper**, all three inequalities: min(U_row, U_col) ≤ ½(U_row + U_col) ≤
--   N/g + |ℛ|(11λ/3 + 8) ≤ N(ρ + 1/g) + 2g⁴, where N = g⁴λ and ρ = 11/12. The second one is Lemma 2(c),
--   the third one |ℛ| ≤ g⁴/4.
--   Same as in the paper (N/g is written g³λ, so that g = 0 needs no exception).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L159-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L159-L187

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

theorem Eight.eqMinTotal_chain (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) :
    ((min (rowNetwork W ι).U (colNetwork W ι).U : ℕ) : ℝ) ≤ (((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U) / 2 ∧
      (((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U) / 2 ≤ (g : ℝ) ^ 3 * lam + #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) ∧
      (g : ℝ) ^ 3 * lam + #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := by sorry
