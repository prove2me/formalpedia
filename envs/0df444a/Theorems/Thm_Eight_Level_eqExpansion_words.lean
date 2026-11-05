-- Prove2me | Theorems.Thm_Eight_Level_eqExpansion_words
-- name    : Eight.Level.eqExpansion_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:31:03.135893+00:00
-- url     : https://prove2.me/theorems/7d99dbe9-4185-4791-bee4-80da7a2c737f
-- title:
--   Level: eq Expansion words
-- statement:
--   **Display (34)** for the clique that the algorithm is given: 2^{t|ℛ|} · Z = ∑_ι Z_ι.
--   `Inst.ZW lam [] Rm` is the value of the (g², λ)-clique whose tables Rm take strings written as
--   lists; the sum is over the numbers y that write the functions ι.
--   From `Eight.eqExpansion`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L64-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L64-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}

theorem Eight.Level.eqExpansion_words (hlam : 1 ≤ lam) (Rm : Inst (Fin (g * g)) (List Bool)) :
    2 ^ (tOf lam * nRect g) * Inst.ZW lam [] Rm = ∑ y ∈ range ((tOf lam + 1) ^ nRect g), Zι (gridR0 g g lam Rm) (Eight.Level.patOf g lam y) := by sorry
