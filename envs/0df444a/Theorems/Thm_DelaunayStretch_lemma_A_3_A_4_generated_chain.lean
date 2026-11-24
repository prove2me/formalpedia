-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_A_3_A_4_generated_chain
-- name    : DelaunayStretch.lemma_A_3_A_4_generated_chain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T00:56:00.493307+00:00
-- url     : https://prove2.me/theorems/6cc3b714-e621-4e33-9898-c3b32a5d956d
-- title:
--   Lemmas A.3–A.4: the faces crossed by $[u,v]$ give a disk chain with $d_D(u,v)\le P(u,v)$
-- statement:
--   Let $S\subset\mathbb R^2$ be finite and let $D$ be a Delaunay triangulation of $S$. Let $u,v\in S$ be two points on the $x$-axis with $x(u)<x(v)$, such that the open segment $(u,v)$ contains no point of $S$ and $[u,v]$ is not an edge of $D$.
--
--   Let $F_1,\dots,F_m$ be the faces of the Delaunay subdivision crossed by $[u,v]$ (Lemma A.2), and let $O_i$ be the closed circumdisk of $F_i$. Then:
--
--   1. (Lemma A.3) $(O_1,\dots,O_m;u,v)$ is a disk chain in the sense of Definition 2.1. Its gates are the common edges $E_i=F_i\cap F_{i+1}$, and each rail is an arc of $\partial O_i$ whose ends are vertices of $F_i$.
--   2. (Lemma A.4) For this chain,
--   $$
--   d_D(u,v)\le P(u,v),
--   $$
--   where $d_D$ is the shortest-path distance along the edges of $D$ and $P(u,v)$ is the shortest-path length in the ladder graph of the chain.
--
--   Together with the chain inequality, this is the core of the reduction from Delaunay triangulations to disk chains (Theorem 2.4). The splitting of $[u,v]$ at points of $S$ and the rigid motion that puts $u,v$ on the $x$-axis are handled in the proof of Theorem 2.4.
--
--   **Formalization Note** The plane is $\mathbb C$. The conclusion asserts that some disk chain $C$ with ends $C.u=u$, $C.v=v$ exists (the chain of Lemma A.3), together with a walk from $u$ to $v$ in the edge graph of $D$ whose Euclidean length is at most $P(u,v)$, the infimum of ladder-walk weights of $C$. This is $d_D(u,v)\le P(u,v)$ without an infimum over walks in $D$.
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979v6, 3 Nov 2026), Appendix A, Lemma A.3 (pp.50–52) and Lemma A.4 (p.52), as used in the proof of Theorem 2.4 (p.52)

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_IsDelaunayTriangulation
import Definitions.Def_DelaunayStretch_delaunayGraph
import Definitions.Def_DelaunayStretch_face

namespace DelaunayStretch

/-- **Lemmas A.3 and A.4 (Generated chains; from rails to paths in `D`)** (pp.50–52).
Let `D` be a Delaunay triangulation of a finite set `S ⊂ ℝ²`, and let `u, v ∈ S` lie on the
`x`-axis with `x(u) < x(v)`, such that the open segment `(u, v)` contains no point of `S` and
`[u, v]` is not an edge of `D`. Then the circumdisks of the faces crossed by `[u, v]` form a disk
chain `(O₁, …, Oₘ; u, v)` (Lemma A.3), and `d_D(u, v) ≤ P(u, v)` for this chain (Lemma A.4).

**Formalization Note** The chain is asserted to exist (Lemma A.3 constructs it from the faces
of Lemma A.2); `d_D(u, v) ≤ P(u, v)` is the existence of a walk from `u` to `v` in the edge
graph of `D` of Euclidean length at most `P(u, v)`. -/
theorem lemma_A_3_A_4_generated_chain (S : Finset ℂ) (D : Finset (Finset ℂ))
    (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S)
    (hopen : ∀ p ∈ S, p ∉ openSegment ℝ u v) (hnot : ¬ IsEdgeOf D u v)
    (huim : u.im = 0) (hvim : v.im = 0) (huv : u.re < v.re) :
    ∃ C : DiskChain, C.IsDiskChain ∧ C.u = u ∧ C.v = v ∧
      ∃ w : (delaunayGraph D).Walk u v, walkLength w ≤ C.shortestPath := by sorry

end DelaunayStretch
