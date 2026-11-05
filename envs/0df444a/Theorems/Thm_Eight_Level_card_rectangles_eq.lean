-- Prove2me | Theorems.Thm_Eight_Level_card_rectangles_eq
-- name    : Eight.Level.card_rectangles_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:46.181822+00:00
-- url     : https://prove2.me/theorems/041ed9ff-736a-4d89-bf9b-94c7bca61d2d
-- title:
--   Level: card rectangles eq
-- statement:
--   The number of rectangles: |ℛ| is `nRect g`, the number that the algorithm uses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L45-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L45-L45

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

theorem Eight.Level.card_rectangles_eq (g : ℕ) : #(rectangles g) = nRect g := by sorry
