-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_theorem_1_membership
-- name    : ArcKayles192.PSPACE.theorem_1_membership
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:23.800646+00:00
-- url     : https://prove2.me/theorems/1ad77e78-b9d8-44af-9460-45effcdcfe17
-- title:
--   Theorem 1, membership half: Arc Kayles is in PSPACE
-- statement:
--   The decision problem ARC KAYLES (given a finite simple graph $G$, does the player to move win Arc Kayles on $G$ under normal play?), with the standard adjacency-matrix encoding of graph instances, is in PSPACE:
--   $$\textsf{ARC KAYLES}\in\mathsf{PSPACE}.$$
--
--   This is the first half of Theorem 1. The proof's estimate (depth-first search of the game tree in space $O(N^3)$) is not part of the claim, which asks only for some polynomial space bound.
--
--   Differences from the source:
--   - encoding: Arc Kayles instances are finite graphs, with no encoding fixed → GraphInstance: n and a symmetric irreflexive Boolean n × n matrix; enc = 1^n 0 followed by the n² adjacency bits row by row; reason: the standard adjacency-matrix encoding, injective, of length n² + n + 1
--   - encoding: Arc Kayles is in PSPACE (a language) → InPSPACE of the published definition constrains the machine only on strings enc(I); reason: well-formedness of the pinned encoding is decidable in polynomial time and space, so the promise form and the language form coincide
--   - encoding: PSPACE, PSPACE-hard, PSPACE-complete in the standard sense → the published OptimalQueuingComplexity.Restless predicates over Mathlib multi-stack machines (FinTM2), space = total stack length, reductions = TM2ComputableInPolyTime; reason: standard machine model; multi-stack machines and Turing machines simulate each other with polynomial overhead
--   - encoding: P-position / N-position defined through winning strategies (p.2) → FirstPlayerWins G S defined by backward induction on |S|; a P-position is its negation; reason: the game tree is finite, so the player to move has a winning strategy iff some move leads to a position not won by the next player to move; determinacy is built in
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.5, proof of Theorem 1 (membership)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace ArcKayles192.PSPACE

open OptimalQueuingComplexity.Restless

/-- **Theorem 1, membership half** (proof of Theorem 1, p.5). ARC KAYLES, with the standard
adjacency-matrix encoding, is in PSPACE. -/
theorem theorem_1_membership : InPSPACE GraphInstance.enc arcKayles := by sorry

end ArcKayles192.PSPACE
