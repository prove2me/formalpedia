-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_theorem_1
-- name    : ArcKayles192.PSPACE.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:40.57379+00:00
-- url     : https://prove2.me/theorems/6037c3fe-22c6-425e-bdb6-3a4475afb51c
-- title:
--   Theorem 1: Arc Kayles is PSPACE-complete
-- statement:
--   The decision problem ARC KAYLES asks, given a finite simple graph $G$, whether the player to move (the first player) wins Arc Kayles on $G$ under normal play. In Arc Kayles two players alternately pick an edge of the current graph and delete both its endpoints, and the first player without a legal move loses. With the standard adjacency-matrix encoding of graphs,
--   $$\textsf{ARC KAYLES}\ \text{is}\ \mathsf{PSPACE}\text{-complete}:$$
--   it is in PSPACE, and every language in PSPACE polynomial-time many-one reduces to it.
--
--   This settles the complexity question Schaefer left open in 1976.
--
--   Differences from the source:
--   - encoding: Arc Kayles instances are finite graphs, with no encoding fixed → GraphInstance: n and a symmetric irreflexive Boolean n × n matrix; enc = 1^n 0 followed by the n² adjacency bits row by row; reason: the standard adjacency-matrix encoding, injective, of length n² + n + 1
--   - encoding: Arc Kayles is in PSPACE (a language) → InPSPACE of the published definition constrains the machine only on strings enc(I); reason: well-formedness of the pinned encoding is decidable in polynomial time and space, so the promise form and the language form coincide
--   - encoding: PSPACE, PSPACE-hard, PSPACE-complete in the standard sense → the published OptimalQueuingComplexity.Restless predicates over Mathlib multi-stack machines (FinTM2), space = total stack length, reductions = TM2ComputableInPolyTime; reason: standard machine model; multi-stack machines and Turing machines simulate each other with polynomial overhead
--   - encoding: P-position / N-position defined through winning strategies (p.2) → FirstPlayerWins G S defined by backward induction on |S|; a P-position is its negation; reason: the game tree is finite, so the player to move has a winning strategy iff some move leads to a position not won by the next player to move; determinacy is built in
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.1, Theorem 1 (restated p.5; proof pp.5–9)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace ArcKayles192.PSPACE

open OptimalQueuingComplexity.Restless

/-- **Theorem 1** (p.1, restated p.5). Arc Kayles is PSPACE-complete: the problem "does the first
player win Arc Kayles under normal play on the given finite simple graph", with the standard
adjacency-matrix encoding, is in PSPACE and PSPACE-hard. -/
theorem theorem_1 : PSPACEComplete GraphInstance.enc arcKayles := by sorry

end ArcKayles192.PSPACE
