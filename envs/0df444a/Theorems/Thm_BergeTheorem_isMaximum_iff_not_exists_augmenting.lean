-- Prove2me | Theorems.Thm_BergeTheorem_isMaximum_iff_not_exists_augmenting
-- name    : BergeTheorem.isMaximum_iff_not_exists_augmenting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:59.177789+00:00
-- url     : https://prove2.me/theorems/f6aa5e28-23cd-5d57-ba4c-f7be641815d4
-- title:
--   Berge Theorem: is Maximum iff not exists augmenting
-- statement:
--   **Berge's theorem (1957).** A matching of a finite graph is maximum if and only if there is no
--   augmenting path.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L47-L51
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L47-L51

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_BergeMatching_isMaximum_iff_not_exists_augmenting

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeTheorem
variable {V : Type*}

theorem BergeTheorem.isMaximum_iff_not_exists_augmenting [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) :
    (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
      ¬ ∃ (u v : V) (p : G.Walk u v), IsAugmentingPath M p := by sorry
