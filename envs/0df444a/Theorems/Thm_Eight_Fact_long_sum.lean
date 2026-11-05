-- Prove2me | Theorems.Thm_Eight_Fact_long_sum
-- name    : Eight.Fact.long_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:54:14.650944+00:00
-- url     : https://prove2.me/theorems/121cbc29-5f42-41db-90e5-1578f6244449
-- title:
--   Fact: long sum
-- statement:
--   «This is a row-wise factorization of A_i through t + 3(t − i) + 6i = 4t + 3i bits. Column-wise
--   the roles of R and C are exchanged, which gives t + 6(t − i) + 3i = 7t − 3i bits.» Both directions
--   at once, for strings a, b (arguments of the first function) and a', b' (of the second): the sum over
--   all θ is the sum over the sets S with i elements of the product over the blocks, as in `StChunk`;
--   row-wise the blocks in S are wide, column-wise the others.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L222-L243
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L222-L243

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.long_sum (hC : StChunk) {tr : Bool} {lam i : ℕ} (hi : i ≤ tOf lam) {a b a' b' : List Bool} (ha : a.length = lam) (ha' : a'.length = lam)
    (hL : useLong tr lam i = true) :
    ∑ θ ∈ words (longCap tr (tOf lam) i), fTop (tr, i, a, b, θ) * fBot (tr, i, a', b', θ) =
      ∑ S ∈ (range (tOf lam)).powersetCard i, ∏ s ∈ range (tOf lam),
        if (decide (s ∈ S) != tr) = true then Rb (blkL a s) (blkL a' s) (blkL b s) (blkL b' s) else Rb (blkL a s) (blkL b s) (blkL a' s) (blkL b' s) := by sorry
