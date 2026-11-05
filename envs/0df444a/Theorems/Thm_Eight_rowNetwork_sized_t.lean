-- Prove2me | Theorems.Thm_Eight_rowNetwork_sized_t
-- name    : Eight.rowNetwork_sized_t
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:06:15.317188+00:00
-- url     : https://prove2.me/theorems/ff3760c1-854e-4c4c-831c-6b3e4a6dccdc
-- title:
--   Eight: row Network sized t
-- statement:
--   «Indeed ∑_{a' ≠ a} c_{a,a'} ≤ g³λ, |W_a| < 2^{gB}, and Ψ_{a,a'} and the functions of its
--   factorization are products of indicators and of g(g−1)/2 numbers of absolute value at most 2^t»: the
--   row network, with the bound 2^{gB + g²t} for all
--   values; the paper then uses 2^t ≤ 2^λ. Different from the paper: values «at most 2^{gB + g²t}» where
--   the paper has «below 2^{B₁}», B₁ = gB + g²λ + 1, and tables with |W_w| ≤ 2^B where the paper has <
--   2^B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L123-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_Grid.lean#L123-L129

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

theorem Eight.rowNetwork_sized_t {B : ℕ} (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) (hW : ∀ w h, |W w h| ≤ 2 ^ B) {ι : Rectangle g → ℕ}
    (hι : ∀ q, ι q ≤ tOf lam) : (rowNetwork W ι).Sized (g ^ 3 * lam) (g * B + g ^ 2 * tOf lam) := by sorry
