-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_claim_8
-- name    : ArcKayles192.PSPACE.claim_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:59.493519+00:00
-- url     : https://prove2.me/theorems/3c5a637b-9a60-4514-84e7-78c4578229f3
-- title:
--   Claim 8: once $b_j$ has no neighbour left in $F$, the move $sa_j$ wins iff $r+k$ is even
-- statement:
--   Let $\varphi$ be a Pos CNF instance with an odd number $m$ of clauses, and let $S$ be a position of Arc Kayles on $G_\varphi$ reached from $V(G_\varphi)$ by assignment and pass moves only, with $r\ge m$. Let $j\in[m]$ be such that $b_j$ has no neighbour left in $F$, i.e. every literal $f_i$ with $x_i\in C_j$ has left $S$. Then the move $sa_j$ is winning (it leads to a P-position) if and only if
--   $$r+k\ \text{is even}.$$
--
--   Differences from the source:
--   - encoding: a position is a graph; isolated vertices are removed automatically (p.3) → a position is a finite set S of remaining vertices of an ambient simple graph G, the current graph being G[S]; isolated vertices stay in S; reason: an isolated vertex carries no move, so outcomes and values are unchanged; every finite graph H is the position (H, all vertices), and every position is the finite graph G[S]
--   - reading: "the first move that is neither an assignment move nor a pass move" / "only assignment and pass moves have been played" → the position S is reachable from the initial position V(G_φ) by legal assignment and pass moves only (ReachableByAP); reason: the claim speaks about the first deviating move of a play; the Lean quantifies over every position such a play can reach
--   - encoding: 1-based indices a_j, b_j (j ∈ [m]), v_i, t_i (i ∈ [R]), f_i (i ∈ [n]), y_i, z_i (i ∈ [K]) → 0-based indices in Fin m, Fin R, Fin n, Fin K; v_i for i ∈ [n] is v ⟨i, _⟩ with i < n; the paper's pass edges v_i t_i, i ∈ [n+1, R], are those with n ≤ i < R; reason: re-indexing only; no instance changes
--   - encoding: r, k (and q) count the remaining vertices of V, Y (and B) after isolated vertices are removed → rCount S = |S ∩ V|, kCount S = |S ∩ Y|; reason: at positions reached by assignment and pass moves every remaining v_i is adjacent to every b_j and every remaining y_i to s, so no vertex of V or Y is isolated and the counts agree
--   - encoding: P-position / N-position defined through winning strategies (p.2) → FirstPlayerWins G S defined by backward induction on |S|; a P-position is its negation; reason: the game tree is finite, so the player to move has a winning strategy iff some move leads to a position not won by the next player to move; determinacy is built in
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.7, Claim 8

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_Construction

namespace ArcKayles192.PSPACE

/-- **Claim 8** (p.7). Let `m` be odd and let `S` be a position of Arc Kayles on `G_φ` reached by
assignment and pass moves only, with `r ≥ m`. If `b_j` has no neighbour left in `F` (every
literal `f_i` of `C_j` is gone from `S`), then the move `s a_j` is winning (it leads to a
P-position) if and only if `r + k` is even. -/
theorem claim_8 (φ : PosCNF) (hm : Odd φ.m) (S : Finset (Vtx φ.n φ.m))
    (hS : ReachableByAP φ S) (hr : φ.m ≤ rCount S) (j : Fin φ.m)
    (hj : ∀ i ∈ φ.clause j, Vtx.f i ∉ S) :
    ¬ FirstPlayerWins (Gphi φ) (S \ {Vtx.s, Vtx.a j}) ↔ Even (rCount S + kCount S) := by sorry

end ArcKayles192.PSPACE
