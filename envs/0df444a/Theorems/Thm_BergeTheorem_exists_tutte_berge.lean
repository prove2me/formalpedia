-- Prove2me | Theorems.Thm_BergeTheorem_exists_tutte_berge
-- name    : BergeTheorem.exists_tutte_berge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:16.46656+00:00
-- url     : https://prove2.me/theorems/182f1d49-6fc8-4685-a7ec-cbe2fbfc57a3
-- title:
--   Berge Theorem: exists tutte berge
-- statement:
--   **The Tutte–Berge formula.** A finite graph has a matching `M` and a vertex set `U` with
--   `2 |M| + odd(G − U) = |V| + |U|`.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L61-L64
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/Solution.lean#L61-L64

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_BergeMatching_exists_tutte_berge

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeTheorem
variable {V : Type*}

theorem BergeTheorem.exists_tutte_berge [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      2 * M.edgeSet.ncard + oddCount G U = Nat.card V + U.ncard := by sorry
