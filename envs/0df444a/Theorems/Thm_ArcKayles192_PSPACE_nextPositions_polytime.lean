-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_nextPositions_polytime
-- name    : ArcKayles192.PSPACE.nextPositions_polytime
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:26:31.740581+00:00
-- url     : https://prove2.me/theorems/a3c028af-7561-4ae3-b378-19198fcdb383
-- title:
--   Ordered-pair enumeration of Arc Kayles successors is polynomial-time computable
-- statement:
--   There is a fixed multi-stack Turing machine which, given the self-delimiting adjacency-matrix encoding of a graph instance $I$ followed by a binary position word $s$, outputs the complete list `nextPositions` of legal successors in time polynomial in the input length. Successors are encoded by concatenating self-delimiting binary words.
--
--   The generating algorithm scans the $n^2$ ordered vertex pairs. For each pair it tests the two relevant position bits and one adjacency bit; for a legal pair it copies the $n$-bit position while clearing the two endpoint bits. Consequently the output has at most $O(n^3)$ bits. Since the graph encoding alone has $n^2+n+1$ bits, both the elementary scan-and-copy work and the output length are polynomial in the actual input length. This supplies the uniform successor-generator requirement for the depth-first polynomial-space game evaluation.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), p.5, proof of Theorem 1 (the game has at most N/2 moves, each position is described by O(N^2) bits, and DFS enumerates the game tree in polynomial space). The child isolates the explicit polynomial-time successor enumeration needed by the formal PolyGame interface; positions here are the more economical N-bit characteristic vectors from Definitions.Def_ArcKayles192_PSPACE_PositionGame.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_Complexity_FiniteGame_PolyGame
import Definitions.Def_ArcKayles192_PSPACE_PositionGame

open ArcKayles192.PSPACE

theorem ArcKayles192.PSPACE.nextPositions_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : GraphInstance × List Bool => Complexity.FiniteGame.tagBits (GraphInstance.enc x.1) ++ x.2)
      Complexity.FiniteGame.encWords (fun x => nextPositions x.1 x.2)) := by sorry
