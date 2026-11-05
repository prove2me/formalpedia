-- Prove2me | Theorems.Thm_Eight_lemPieces_b_row
-- name    : Eight.lemPieces_b_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:55:08.640858+00:00
-- url     : https://prove2.me/theorems/d5f0ecd0-f440-42cc-ab91-8beb2f5957ac
-- title:
--   Eight: lem Pieces b row
-- statement:
--   Lemma 2(b), row-wise half of its first sentence, with the bound of its second sentence: «As a
--   function of (x,y) and (u,v), A_i factors through c_i^row bits», with values at most 2^t in absolute
--   value. The field `b_row` of `Eight.LemPieces`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L286-L288
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L286-L288

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset

theorem Eight.lemPieces_b_row (h : StFact) (lam i : ℕ) (hlam : 1 ≤ lam) (hi : i ≤ tOf lam) : FactorsLe (Pieces.rowwise (A lam i)) (crow lam i) (2 ^ tOf lam) := by sorry
