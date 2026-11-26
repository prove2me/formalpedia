-- Prove2me | Theorems.Thm_BergeMatching_two_mul_card_add_le
-- name    : BergeMatching.two_mul_card_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:52:58.272588+00:00
-- url     : https://prove2.me/theorems/be732c1b-836a-50ce-8c89-ed605e0547a4
-- title:
--   Berge Matching: two mul card add le
-- statement:
--   **Weak Tutte–Berge inequality.** For every matching `M` and vertex set `U` of a finite graph,
--   `2 |M| + odd(G − U) ≤ |V| + |U|`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/BergeLib/Berge.lean#L522-L568
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/BergeLib/Berge.lean#L522-L568

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeMatching
variable {V : Type*}

theorem BergeMatching.two_mul_card_add_le [Finite V] {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (U : Set V) : 2 * M.edgeSet.ncard + oddCount G U ≤ Nat.card V + U.ncard := by sorry
