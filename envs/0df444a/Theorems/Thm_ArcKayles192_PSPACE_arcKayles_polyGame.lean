-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_arcKayles_polyGame
-- name    : ArcKayles192.PSPACE.arcKayles_polyGame
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:41:21.100005+00:00
-- url     : https://prove2.me/theorems/8922e289-e9e7-4566-83f5-29f8d8878486
-- title:
--   Arc Kayles is a polynomially presented finite game with the same winning predicate
-- statement:
--   There is a polynomially presented finite impartial game $G$, in the sense of the generic `PolyGame` interface, whose instances are the published adjacency-matrix graph instances and whose initial-position winning predicate is exactly ARC KAYLES:
--   $$
--   G.\operatorname{enc}=G_{\mathrm{graph}}.\operatorname{enc},
--   \qquad
--   W_G(I,s_0(I))\ \Longleftrightarrow\ \operatorname{FirstPlayerWins}(I.\operatorname{graph},V(I)).
--   $$
--   A position is the $N$-bit characteristic vector of the remaining vertex set. The successor generator enumerates the ordered pairs $u,v$ and, whenever $uv$ is an edge with both endpoints present, outputs the vector with those two bits cleared. Its output has $O(N^3)$ bits, so it is polynomial-time computable in the adjacency-matrix input length. The rank is the number of remaining vertices; it decreases by at least one on every move. These are the position representation and rank decrease used in the paper's depth-first search argument.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), p.2 (Arc Kayles positions, legal moves, and normal-play outcome) and p.5, proof of Theorem 1 (at most N/2 moves, O(N^2) bits per position). Specializes the generic `PolyGame` interface to the published `GraphInstance` encoding.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_Complexity_FiniteGame_PolyGame

open ArcKayles192.PSPACE

theorem ArcKayles192.PSPACE.arcKayles_polyGame :
    ∃ G : Complexity.FiniteGame.PolyGame GraphInstance,
      G.enc = GraphInstance.enc ∧
      ∀ I, G.wins I (G.start I) ↔ arcKayles I := by sorry
