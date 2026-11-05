-- Prove2me | Theorems.Thm_Eight_sum_words_six
-- name    : Eight.sum_words_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:52:15.637885+00:00
-- url     : https://prove2.me/theorems/15bb2eda-d35f-4f16-9fc0-6257e5f2b9fe
-- title:
--   Eight: sum words six
-- statement:
--   A sum over the words of 6 bits is a sum over the pairs of blocks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L82-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L82-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset

theorem Eight.sum_words_six {X : Type*} [AddCommMonoid X] (G : Block → Block → X) :
    ∑ w ∈ words 6, G (blkAt w 0) (blkAt w 3) = ∑ k : Block, ∑ k' : Block, G k k' := by sorry
