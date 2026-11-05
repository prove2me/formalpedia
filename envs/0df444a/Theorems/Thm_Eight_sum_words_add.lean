-- Prove2me | Theorems.Thm_Eight_sum_words_add
-- name    : Eight.sum_words_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:27:26.744339+00:00
-- url     : https://prove2.me/theorems/0dde8232-2bbf-4dc4-bcc8-07e385dcdda2
-- title:
--   Eight: sum words add
-- statement:
--   A sum over the words of m + n bits is a double sum: a word of m bits followed by a word of n
--   bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L34-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L34-L52

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

theorem Eight.sum_words_add {X : Type*} [AddCommMonoid X] (m n : ℕ) (G : List Bool → X) :
    ∑ w ∈ words (m + n), G w = ∑ u ∈ words m, ∑ v ∈ words n, G (u ++ v) := by sorry
