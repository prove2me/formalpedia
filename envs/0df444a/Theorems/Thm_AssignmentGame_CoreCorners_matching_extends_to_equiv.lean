-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_matching_extends_to_equiv
-- name    : AssignmentGame.CoreCorners.matching_extends_to_equiv
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:08:51.578281+00:00
-- url     : https://prove2.me/theorems/a74e37fd-493c-4af0-9a7d-9646416ab502
-- title:
--   Every partial matching in a complete balanced bipartite graph extends to a perfect matching
-- statement:
--   Suppose two finite vertex sets have the same size, witnessed by a bijection $e:M\simeq N$. Every partial matching $P$ between them extends to a perfect matching: there is a bijection $f:M\simeq N$ with $f(i)=j$ for each edge $(i,j)$ of $P$.
--
--   This completion principle lets nonnegative matching gains be compared with full courier–order assignments.
-- source:
--   Finite matching extension principle; https://arxiv.org/abs/2507.10872, Section 3.1, Lemma 3.3, courier–order assignment argument.

import Definitions.Def_AssignmentGame_CoreCorners_Game

namespace AssignmentGame.CoreCorners

theorem matching_extends_to_equiv {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (e : M ≃ N) (P : Finset (M × N))
    (hP : IsMatching Finset.univ Finset.univ P) :
    ∃ f : M ≃ N, ∀ p ∈ P, f p.1 = p.2 := by sorry

end AssignmentGame.CoreCorners
