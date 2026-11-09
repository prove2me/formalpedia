-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_claim_7
-- name    : ArcKayles192.PSPACE.claim_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:54.70238+00:00
-- url     : https://prove2.me/theorems/d3a9531e-dbbe-46f6-b80e-68c8ce408130
-- title:
--   Claim 7: while $r\ge m$ and $k\ge 1$, the first move that is neither an assignment nor a pass move loses, except $sa_j$ once all literals of $C_j$ in $F$ are gone
-- statement:
--   Let $\varphi$ be a Pos CNF instance with an odd number $m$ of clauses (the standing assumption of the proof of Theorem 1, p.5), and let $S$ be a position of Arc Kayles on $G_\varphi$ reached from $V(G_\varphi)$ by assignment and pass moves only. Assume
--   $$r\ge m\qquad\text{and}\qquad k\ge 1.$$
--   Let $uw$ be a legal move from $S$ that is neither an assignment move nor a pass move, and that is not an edge $sa_j$ for which every literal $f_i$ of $C_j$ has left $S$. Then the move $uw$ loses: the opponent, who moves next at $S\setminus\{u,w\}$, wins.
--
--   Differences from the source:
--   - encoding: a position is a graph; isolated vertices are removed automatically (p.3) → a position is a finite set S of remaining vertices of an ambient simple graph G, the current graph being G[S]; isolated vertices stay in S; reason: an isolated vertex carries no move, so outcomes and values are unchanged; every finite graph H is the position (H, all vertices), and every position is the finite graph G[S]
--   - reading: "the first move that is neither an assignment move nor a pass move" / "only assignment and pass moves have been played" → the position S is reachable from the initial position V(G_φ) by legal assignment and pass moves only (ReachableByAP); reason: the claim speaks about the first deviating move of a play; the Lean quantifies over every position such a play can reach
--   - encoding: 1-based indices a_j, b_j (j ∈ [m]), v_i, t_i (i ∈ [R]), f_i (i ∈ [n]), y_i, z_i (i ∈ [K]) → 0-based indices in Fin m, Fin R, Fin n, Fin K; v_i for i ∈ [n] is v ⟨i, _⟩ with i < n; the paper's pass edges v_i t_i, i ∈ [n+1, R], are those with n ≤ i < R; reason: re-indexing only; no instance changes
--   - encoding: r, k (and q) count the remaining vertices of V, Y (and B) after isolated vertices are removed → rCount S = |S ∩ V|, kCount S = |S ∩ Y|; reason: at positions reached by assignment and pass moves every remaining v_i is adjacent to every b_j and every remaining y_i to s, so no vertex of V or Y is isolated and the counts agree
--   - encoding: "loses" → FirstPlayerWins (G_φ) (S \ {u, w}): the player to move after the deviation wins; reason: normal-play reading of losing a move
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.6, Claim 7 (proof pp.6–7)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_Construction

namespace ArcKayles192.PSPACE

/-- **Claim 7** (p.6). Let `m` be odd and let `S` be a position of Arc Kayles on `G_φ` reached by
assignment and pass moves only, with `r ≥ m` and `k ≥ 1`. Then every legal move `uw` from `S`
that is neither an assignment move nor a pass move loses (the opponent, to move next, wins),
except the moves `s a_j` such that every literal `f_i` of `C_j` is gone from `S`. -/
theorem claim_7 (φ : PosCNF) (hm : Odd φ.m) (S : Finset (Vtx φ.n φ.m))
    (hS : ReachableByAP φ S) (hr : φ.m ≤ rCount S) (hk : 1 ≤ kCount S)
    (u w : Vtx φ.n φ.m) (hu : u ∈ S) (hw : w ∈ S) (huw : (Gphi φ).Adj u w)
    (hna : ¬ IsAssignMove φ u w) (hnp : ¬ IsPassMove φ u w)
    (hexc : ¬ ∃ j : Fin φ.m, s(u, w) = s(Vtx.s, Vtx.a j) ∧ ∀ i ∈ φ.clause j, Vtx.f i ∉ S) :
    FirstPlayerWins (Gphi φ) (S \ {u, w}) := by sorry

end ArcKayles192.PSPACE
