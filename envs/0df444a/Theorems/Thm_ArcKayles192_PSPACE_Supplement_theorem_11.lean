-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_Supplement_theorem_11
-- name    : ArcKayles192.PSPACE.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:18:46.147026+00:00
-- url     : https://prove2.me/theorems/b01c6834-5519-46e2-bfb3-dca73bfbb1e9
-- title:
--   Theorem 11: Misère Arc Kayles is PSPACE-complete
-- statement:
--   The decision problem MISÈRE ARC KAYLES asks, given a finite simple graph $G$, whether the player to move (the first player) wins Arc Kayles on $G$ under misère play. Two players alternately pick an edge of the current graph and delete both its endpoints, and the first player without a legal move **wins**. With the standard adjacency-matrix encoding of graphs,
--   $$\textsf{MISÈRE ARC KAYLES}\ \text{is}\ \mathsf{PSPACE}\text{-complete}:$$
--   it is in PSPACE, and every language in PSPACE polynomial-time many-one reduces to it.
--
--   This is the misère counterpart of Theorem 1, the mission's goal: the end-of-play convention is reversed, while instances, encoding and complexity notions are the same.
--
--   Differences from the source:
--   - encoding: Arc Kayles instances are finite graphs, with no encoding fixed → GraphInstance: n and a symmetric irreflexive Boolean n × n matrix; enc = 1^n 0 followed by the n² adjacency bits row by row; reason: the standard adjacency-matrix encoding, injective, of length n² + n + 1, the same as for Theorem 1
--   - encoding: misère Arc Kayles is in PSPACE (a language) → InPSPACE of the published definition constrains the machine only on strings enc(I); reason: well-formedness of the pinned encoding is decidable in polynomial time and space, so the promise form and the language form coincide
--   - encoding: PSPACE, PSPACE-hard, PSPACE-complete in the standard sense → the published OptimalQueuingComplexity.Restless predicates over Mathlib multi-stack machines (FinTM2), space = total stack length, reductions = TM2ComputableInPolyTime; reason: standard machine model; multi-stack machines and Turing machines simulate each other with polynomial overhead
--   - encoding: winning under misère play, through winning strategies (pp.2, 9) → FirstPlayerWinsMisere G S defined by backward induction on |S|, true when no legal move remains; reason: the game tree is finite, so the player to move has a winning strategy iff the position has no move or some move leads to a position not won by the next player to move
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.9, Theorem 11 (proof sketch pp.9–10)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_Supplement_Misere
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace ArcKayles192.PSPACE.Supplement

open OptimalQueuingComplexity.Restless

/-- **Theorem 11** (p.9). Misère Arc Kayles is PSPACE-complete: the problem "does the first
player win Arc Kayles under misère play (the first player without a legal move wins) on the given
finite simple graph", with the standard adjacency-matrix encoding, is in PSPACE and
PSPACE-hard. -/
theorem theorem_11 : PSPACEComplete GraphInstance.enc misereArcKayles := by sorry

end ArcKayles192.PSPACE.Supplement
