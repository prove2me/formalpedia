-- Prove2me | Theorems.Thm_Eight_A_eq_sum_subsets
-- name    : Eight.A_eq_sum_subsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:55.060624+00:00
-- url     : https://prove2.me/theorems/dc8eac07-0b14-4486-9ebf-6e868be26c20
-- title:
--   Eight: A eq sum subsets
-- statement:
--   A sentence of the proof of Lemma 2(b): «A_i is the sum, over the sets Q ⊆ [t] with |Q| = i, of
--   the product that takes C at the blocks s ∈ Q and R at the others.» The statement is this sentence of
--   the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L69-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L69-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
set_option autoImplicit false
section
section
open Eight
open Finset Polynomial

theorem Eight.A_eq_sum_subsets (lam i : ℕ) (x y u v : Pieces.Bits lam) :
    A lam i x y u v = ∑ Q ∈ (Finset.range (tOf lam)).powersetCard i, ∏ s ∈ Finset.range (tOf lam),
      if s ∈ Q then Cb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) else Rb (blockAt x s) (blockAt y s) (blockAt u s) (blockAt v s) := by sorry
