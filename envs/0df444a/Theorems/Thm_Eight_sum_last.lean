-- Prove2me | Theorems.Thm_Eight_sum_last
-- name    : Eight.sum_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:52:37.382448+00:00
-- url     : https://prove2.me/theorems/27d7a118-0276-4a80-b078-4bf519a06102
-- title:
--   Eight: sum last
-- statement:
--   A block that is not wide: Σ_k ψ_k(a,b)·ψ_k(b',a') = R(a,b,a',b'), the definition of R. A wide
--   block: Σ_{k,k'} [(a,b) = (k,k')]·R(k,a',k',b') = R(a,a',b,b'), the factorization through all 6 bits
--   of (a,b). Here u is the part
--   of θ' before the index of the block number t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L139-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L139-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset

theorem Eight.sum_last (tr : Bool) (t : ℕ) (Q a b a' b' : List Bool) {u : List Bool} (hu : u.length = lenW tr Q t) :
    ∑ v ∈ words (if wide tr Q t = true then 6 else 3), topAt tr Q (u ++ v) a b t * botAt tr Q (u ++ v) a' b' t =
      if wide tr Q t = true then Rb (blkL a t) (blkL a' t) (blkL b t) (blkL b' t) else Rb (blkL a t) (blkL b t) (blkL a' t) (blkL b' t) := by sorry
