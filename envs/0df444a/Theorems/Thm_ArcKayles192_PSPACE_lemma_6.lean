-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_lemma_6
-- name    : ArcKayles192.PSPACE.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:34.648746+00:00
-- url     : https://prove2.me/theorems/20890ca0-bade-4307-bd0f-2cb264fc34e2
-- title:
--   Lemma 6: a biclique $K_{a,b}$ whose vertices have private pendants, plus an independent set, has value $g(a,b)$
-- statement:
--   Let $H$ be a simple graph and $S$ a position on it, partitioned into $B=B_1\cup B_2$ and $I$, such that
--
--   1. $H[B]$ is an induced biclique with sides $B_1$ and $B_2$: two vertices of $B$ are adjacent iff they lie on different sides (in particular $B_1\cap B_2=\emptyset$); write $a=|B_1|$ and $b=|B_2|$, which may be $0$;
--   2. $I$ is an independent set;
--   3. every vertex $u\in B$ has a neighbour $w\in I$ of degree $1$ in $H[S]$, i.e. $u$ is the only neighbour of $w$ in $S$.
--
--   Vertices of $I$ may have any degree, and the edges between $B$ and $I$ are otherwise arbitrary. Then
--   $$\mathrm{sg}(H,S)=g(a,b):=(a+b)\bmod 2+2\cdot(\min(a,b)\bmod 2).$$
--
--   This exact formula is what makes every cheating move in $G_\varphi$ computable (Claims 7–10).
--
--   Differences from the source:
--   - encoding: a position is a graph; isolated vertices are removed automatically (p.3) → a position is a finite set S of remaining vertices of an ambient simple graph G, the current graph being G[S]; isolated vertices stay in S; reason: an isolated vertex carries no move, so outcomes and values are unchanged; every finite graph H is the position (H, all vertices), and every position is the finite graph G[S]
--   - encoding: V(H) is partitioned into B, I with H[B] an induced biclique isomorphic to K_{a,b} → B₁ ∪ B₂ ∪ I = S, B₁ ∪ B₂ disjoint from I, and for u, w ∈ B₁ ∪ B₂: Adj u w ↔ (u ∈ B₁ ↔ w ∈ B₂); a = |B₁|, b = |B₂|; reason: this is the definition of an induced K_{a,b}; it forces B₁ ∩ B₂ = ∅ because the graph is loopless
--   - encoding: a neighbor in I that has degree 1 (in H) → w ∈ I adjacent to u whose only neighbour in S is u; reason: the degree of w in H = G[S] counts its neighbours in S
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.4, Lemma 6

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

namespace ArcKayles192.PSPACE

/-- **Lemma 6** (p.4). Let the position `S` of `H` be partitioned into `B = B₁ ∪ B₂` and `I`, where
`H[B]` is the induced biclique with sides `B₁`, `B₂` (two vertices of `B` are adjacent iff they lie
on different sides; this forces `B₁ ∩ B₂ = ∅`), `I` is independent, and every vertex of `B` has a
neighbour in `I` whose only neighbour in `S` is that vertex. Then `sg(H[S]) = g(|B₁|, |B₂|)`. -/
theorem lemma_6 {W : Type*} [DecidableEq W] (H : SimpleGraph W) (S B₁ B₂ I : Finset W)
    (hcover : B₁ ∪ B₂ ∪ I = S) (hdisj : Disjoint (B₁ ∪ B₂) I)
    (hbic : ∀ u ∈ B₁ ∪ B₂, ∀ w ∈ B₁ ∪ B₂, H.Adj u w ↔ (u ∈ B₁ ↔ w ∈ B₂))
    (hind : ∀ u ∈ I, ∀ w ∈ I, ¬ H.Adj u w)
    (hpend : ∀ u ∈ B₁ ∪ B₂, ∃ w ∈ I, H.Adj u w ∧ ∀ x ∈ S, H.Adj w x → x = u) :
    sg H S = g B₁.card B₂.card := by sorry

end ArcKayles192.PSPACE
