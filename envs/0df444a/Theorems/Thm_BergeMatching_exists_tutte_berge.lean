-- Prove2me | Theorems.Thm_BergeMatching_exists_tutte_berge
-- name    : BergeMatching.exists_tutte_berge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:53:06.235344+00:00
-- url     : https://prove2.me/theorems/4718317e-c65a-4a49-bfad-e543f8055bed
-- title:
--   Berge Matching: exists tutte berge
-- statement:
--   **The Tutte–Berge formula.** A finite graph has a matching `M` and a vertex set `U` with
--   `2 |M| + odd(G − U) = |V| + |U|`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/BergeLib/Berge.lean#L572-L628
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/BergeLib/Berge.lean#L572-L628

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeMatching
variable {V : Type*}

theorem BergeMatching.exists_tutte_berge [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      2 * M.edgeSet.ncard + oddCount G U = Nat.card V + U.ncard := by sorry
