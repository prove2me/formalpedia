-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_lemma_3
-- name    : ArcKayles192.PSPACE.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:22.648743+00:00
-- url     : https://prove2.me/theorems/8d5172a7-0e5b-43bf-859e-1b8bbf01d8fb
-- title:
--   Lemma 3: a position is a P-position iff its Sprague–Grundy value is $0$
-- statement:
--   Let $G$ be a simple graph and $S$ a position of Arc Kayles on it. Then the player to move at $S$ loses under normal play (that is, $S$ is a P-position) if and only if
--   $$\mathrm{sg}(G,S)=0.$$
--
--   This links outcomes, which the reduction must control, to values, which Lemmas 4 and 6 compute.
--
--   Differences from the source:
--   - encoding: a position is a graph; isolated vertices are removed automatically (p.3) → a position is a finite set S of remaining vertices of an ambient simple graph G, the current graph being G[S]; isolated vertices stay in S; reason: an isolated vertex carries no move, so outcomes and values are unchanged; every finite graph H is the position (H, all vertices), and every position is the finite graph G[S]
--   - encoding: P-position / N-position defined through winning strategies (p.2) → FirstPlayerWins G S defined by backward induction on |S|; a P-position is its negation; reason: the game tree is finite, so the player to move has a winning strategy iff some move leads to a position not won by the next player to move; determinacy is built in
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.3, Lemma 3

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

namespace ArcKayles192.PSPACE

/-- **Lemma 3** (p.3). A position is a P-position (the player to move does not win under normal
play) if and only if its Sprague–Grundy value is `0`. -/
theorem lemma_3 {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    ¬ FirstPlayerWins G S ↔ sg G S = 0 := by sorry

end ArcKayles192.PSPACE
