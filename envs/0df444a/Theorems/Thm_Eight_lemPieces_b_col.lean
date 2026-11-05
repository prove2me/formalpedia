-- Prove2me | Theorems.Thm_Eight_lemPieces_b_col
-- name    : Eight.lemPieces_b_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:54:33.862314+00:00
-- url     : https://prove2.me/theorems/3b6ac3df-cc20-4aff-8d3b-f1cf2b78c311
-- title:
--   Eight: lem Pieces b col
-- statement:
--   Lemma 2(b), column-wise half of its first sentence, with the bound of its second sentence: «as a
--   function of (x,u) and (y,v), through c_i^col bits», with values at most 2^t in absolute value. The
--   field `b_col` of `Eight.LemPieces`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L293-L295
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L293-L295

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

theorem Eight.lemPieces_b_col (h : StFact) (lam i : ℕ) (hlam : 1 ≤ lam) (hi : i ≤ tOf lam) : FactorsLe (Pieces.colwise (A lam i)) (ccol lam i) (2 ^ tOf lam) := by sorry
