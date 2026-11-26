-- Prove2me | Theorems.Thm_BergeMatching_isMaximum_iff_not_exists_augmenting
-- name    : BergeMatching.isMaximum_iff_not_exists_augmenting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:08.389904+00:00
-- url     : https://prove2.me/theorems/97e94403-00ff-4fa2-b44f-4fcc90db7c2e
-- title:
--   Berge Matching: is Maximum iff not exists augmenting
-- statement:
--   **Berge's theorem (1957).** A matching of a finite graph is maximum if and only if there is no
--   augmenting path.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/BergeLib/Berge.lean#L505-L518
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/BergeLib/Berge.lean#L505-L518

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeMatching
variable {V : Type*}

theorem BergeMatching.isMaximum_iff_not_exists_augmenting [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) :
    (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
      ¬ ∃ (u v : V) (p : G.Walk u v), IsAugmentingPath M p := by sorry
