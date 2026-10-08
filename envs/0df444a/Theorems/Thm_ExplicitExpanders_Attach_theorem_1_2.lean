-- Prove2me | Theorems.Thm_ExplicitExpanders_Attach_theorem_1_2
-- name    : ExplicitExpanders.Attach.theorem_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:37:56.613519+00:00
-- url     : https://prove2.me/theorems/54d4b856-b7d4-4ff1-90ab-0bd33085d2f4
-- title:
--   Theorem 1.2 (spectral core): attaching $r$ vertices to a $(p+1)$-regular Ramanujan graph and adding loops gives an $(m+r,\,p+2,\,\sqrt{2(p+1)}+\sqrt p+(p+1)r/m)$-graph
-- statement:
--   Let $p\ge 0$ and $m\ge 1$ be integers, and let $H$ be a $(p+1)$-regular simple graph on a vertex set $V$ of $m$ vertices in which every nontrivial eigenvalue has absolute value at most $2\sqrt p$ (an $(m,p+1,2\sqrt p)$-graph, i.e. a Ramanujan graph). Let $R=\{u_1,\dots,u_r\}$ be $r$ new vertices, and let $W_1,\dots,W_r\subseteq V$ be pairwise disjoint sets of exactly $p+2$ vertices each. Form the graph $G$ on $V\cup R$ by joining each $u_i$ to every vertex of $W_i$ and adding one loop at each vertex of $V\setminus\bigcup_iW_i$, where a loop adds one to the degree. Then $G$ is an $(m+r,\;p+2,\;\lambda)$-graph with
--   $$\lambda=\sqrt{2(p+1)}+\sqrt p+\frac{(p+1)\,r}{m}:$$
--   its adjacency matrix $A_G$ is symmetric, every row sums to $d=p+2$, and every eigenvalue $\mu$ of $A_G$ with an eigenvector orthogonal to the constant vector satisfies $|\mu|\le\lambda$.
--
--   In the paper, Theorem 1.2 reads: for any prime $p\equiv1 \pmod 4$ and every sufficiently large $n$ there is a strongly explicit construction of an $(n,d,\lambda)$-graph on exactly $n$ vertices with $d=p+2$ and $\lambda\le\sqrt{2(d-1)}+\sqrt{d-1}+o(1)$. Its proof takes $H$ to be the Lubotzky–Phillips–Sarnak graph on $m=|SL(2,\mathbb F_q)|$ vertices for a suitable prime $q$, sets $r=n-m$, and proves the bound $\sqrt{2(p+1)}+\sqrt p+o(1)$ stated here. The paper writes $o(1)$; the proof yields $(p+1)r/m$, which tends to $0$ because $r=n-m=o(m)$ by the distribution of primes in progressions (p. 8). The statement is the spectral content of Theorem 1.2: it turns any Ramanujan graph on $m$ vertices into a near-Ramanujan graph of degree one higher on any number $n=m+r$ of vertices with $(p+2)r\le m$, at the cost of a factor of about $(1+\sqrt2)/2$ in the eigenvalue bound.
--
--   **Formalization Note** The bound uses $\sqrt p=\sqrt{d-2}$, as in the proof and in the paper's abstract, which is stronger than the printed $\sqrt{d-1}$ of Theorem 1.2. The primality of $p$ and $p\equiv1\pmod 4$ serve only to obtain $H$ from the Lubotzky–Phillips–Sarnak construction, so they are not assumed: $H$ is an arbitrary graph with the spectral property. The existence of $q$, the estimate $n-m=o(m)$, the numbering of $SL(2,\mathbb F_q)$, and the explicitness of the construction are not part of this statement. The graph $G$ is represented by its adjacency matrix on $V\oplus\mathrm{Fin}\,r$, since it has loops.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 3, Theorem 1.2; proof in Section 2.4, pp. 8-9

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

namespace ExplicitExpanders.Attach

/-- Theorem 1.2 (arXiv:2003.11673v1, p. 3), spectral core as proved on pp. 8–9, with the
paper's `o(1)` made explicit as `(p+1) r / m`: let `H` be a `(p+1)`-regular graph on `m ≥ 1`
vertices whose nontrivial eigenvalues have absolute value at most `2√p`, and let `W i`
(`i < r`) be pairwise disjoint sets of `p + 2` vertices of `H`. Attach `r` new vertices,
the `i`-th joined to `W i`, and put one loop at every other vertex of `H`. The resulting
graph `G` (adjacency matrix `matG H W`) is an `(m + r, p + 2, λ)`-graph with
`λ = √(2(p+1)) + √p + (p+1) r / m`. -/
theorem theorem_1_2 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p m r : ℕ) (hH : IsNDLambda H m (p + 1) (2 * Real.sqrt p))
    (W : Fin r → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hcard : ∀ i, (W i).card = p + 2) :
    IsNDLambdaMatrix (matG H W) (m + r) (p + 2)
      (Real.sqrt (2 * ((p : ℝ) + 1)) + Real.sqrt p + ((p : ℝ) + 1) * r / m) := by sorry

end ExplicitExpanders.Attach
