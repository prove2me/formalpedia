-- Prove2me | Theorems.Thm_Eight_Fact_sum_words_count
-- name    : Eight.Fact.sum_words_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:53:17.028076+00:00
-- url     : https://prove2.me/theorems/2de7dafd-4686-4c76-93b6-8092062844b5
-- title:
--   Fact: sum words count
-- statement:
--   «A set Q ⊆ [t] is written as a string of t bits»: a sum over the words of t bits with i ones is
--   the sum over the subsets of {0, …, t − 1} with i elements. The summand is a product over the
--   positions s of a function of s and of «s ∈ Q».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L94-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L94-L132

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.sum_words_count (t i : ℕ) (g : ℕ → Bool → ℤ) :
    ∑ Q ∈ words t, (if Q.count true = i then ∏ s ∈ range t, g s (Q.getD s false) else 0) =
      ∑ S ∈ (range t).powersetCard i, ∏ s ∈ range t, g s (decide (s ∈ S)) := by sorry
