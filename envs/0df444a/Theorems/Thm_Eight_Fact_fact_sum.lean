-- Prove2me | Theorems.Thm_Eight_Fact_fact_sum
-- name    : Eight.Fact.fact_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:54:23.071277+00:00
-- url     : https://prove2.me/theorems/d4474b58-9503-4aa7-b2ba-b33b611dcf93
-- title:
--   Fact: fact sum
-- statement:
--   The two factorizations of A_i, over words; tr = false: row-wise, c_i^row = min{2λ, 4t + 3i}
--   bits; tr = true: column-wise, c_i^col = min{2λ, 7t − 3i} bits. «Whenever one of these numbers
--   exceeds 2λ, use the factorization through 2λ bits instead.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L253-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L253-L265

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
open Eight.Fact

theorem Eight.Fact.fact_sum (hC : StChunk) (hA : StAMul) (hS : StSubsets) (tr : Bool) {lam i : ℕ} (hi : i ≤ tOf lam) (x y u v : Pieces.Bits lam) :
    A lam i x y u v = ∑ θ ∈ words (min (2 * lam) (longCap tr (tOf lam) i)),
      fTop (tr, i, List.ofFn x, List.ofFn (bif tr then u else y), θ) * fBot (tr, i, List.ofFn (bif tr then y else u), List.ofFn v, θ) := by sorry
