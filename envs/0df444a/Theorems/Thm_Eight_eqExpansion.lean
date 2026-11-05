-- Prove2me | Theorems.Thm_Eight_eqExpansion
-- name    : Eight.eqExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:06:09.291472+00:00
-- url     : https://prove2.me/theorems/4dbdd516-3a6e-4cb3-8bfb-78950bc4ec3c
-- title:
--   Eight: eq Expansion
-- statement:
--   **Display (34) of the paper**: 2^{t|ℛ|} · Z = ∑_ι Z_ι, the sum over all ι : ℛ → {0, …, t}.
--   «Multiply Z by 2^{t|ℛ|}, apply Lemma 2(a) to every rectangle, and expand.»
--   Here Z = `W.Z d` is the value of the clique with tables W on a node set J with g² elements, with one
--   string per edge: Z = ∑ over all choices of one string per edge of ∏_w W_w(the strings on the edges
--   at w).
--   Different from the paper: the nodes are identified with the grid points by an arbitrary bijection e;
--   a table W_w is a function of one string for every node w', where the entry at w' = w is a dummy that
--   is always the fixed string d
--   (`Grid.onGrid` carries the tables to the grid and makes them 0 unless the dummy entry is d).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L66-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L66-L70

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

theorem Eight.eqExpansion {J : Type} [Fintype J] [LinearOrder J] (hlam : 1 ≤ lam) (W : Inst J (Bits lam)) (d : Bits lam) (e : J ≃ Fin g × Fin g) :
    2 ^ (tOf lam * #(rectangles g)) * W.Z d = ∑ ι ∈ patterns g lam, Zι (Grid.onGrid W d e) ι := by sorry
