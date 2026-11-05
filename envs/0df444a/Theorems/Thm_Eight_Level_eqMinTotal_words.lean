-- Prove2me | Theorems.Thm_Eight_Level_eqMinTotal_words
-- name    : Eight.Level.eqMinTotal_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:07:43.169068+00:00
-- url     : https://prove2.me/theorems/99a987fb-6c76-475f-aea9-d0bdc2a14e06
-- title:
--   Level: eq Min Total words
-- statement:
--   **Display (36)** for the two networks that the algorithm runs: min(U_row, U_col) ≤ N(ρ + 1/g) +
--   2g⁴, N = g⁴λ, ρ = 11/12. From `Eight.eqMinTotal`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L136-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L136-L139

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

theorem Eight.Level.eqMinTotal_words (hlam : 1 ≤ lam) (g y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    ((min (netOfι g false lam y Rm).U (netOfι g true lam y Rm).U : ℕ) : ℝ) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := by sorry
