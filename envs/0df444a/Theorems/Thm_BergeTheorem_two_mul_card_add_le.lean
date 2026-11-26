-- Prove2me | Theorems.Thm_BergeTheorem_two_mul_card_add_le
-- name    : BergeTheorem.two_mul_card_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:02.999578+00:00
-- url     : https://prove2.me/theorems/0e7f7ebb-b586-5e36-aea4-1aecb672a5a8
-- title:
--   Berge Theorem: two mul card add le
-- statement:
--   **Weak Tutte–Berge inequality.** For every matching `M` and vertex set `U` of a finite graph,
--   `2 |M| + odd(G − U) ≤ |V| + |U|`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L55-L57
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L55-L57

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_BergeMatching_two_mul_card_add_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeTheorem
variable {V : Type*}

theorem BergeTheorem.two_mul_card_add_le [Finite V] {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (U : Set V) : 2 * M.edgeSet.ncard + oddCount G U ≤ Nat.card V + U.ncard := by sorry
