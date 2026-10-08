-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_theorem_1_3
-- name    : ExplicitExpanders.Delete.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:15:27.450429+00:00
-- url     : https://prove2.me/theorems/5734fd04-6434-42f2-8a63-8de21a94c2dc
-- title:
--   Theorem 1.3 — $(n,d,\lambda)$-graphs with $\lambda\le 2\sqrt{d-1}+\varepsilon$ on every admissible number of vertices
-- statement:
--   Let $d\ge3$ be an integer, $\varepsilon>0$, and $r = \lceil 2/\varepsilon\rceil$. Let $H$ be a finite simple graph on $N$ vertices such that
--
--   1. $H$ is an $(N, d, 2\sqrt{d-1}+\varepsilon/2)$-graph;
--   2. the $(2r+4)$-neighbourhood of every vertex of $H$ contains at most one cycle;
--   3. $r\le \log_{d-1} N$.
--
--   Then for every integer $u\ge0$ with
--   $$u \le \frac{N}{2d^{2r+3}} \quad\text{and}\quad ud \text{ even},$$
--   there is an $(N-u,\; d,\; 2\sqrt{d-1}+\varepsilon)$-graph on exactly $N-u$ vertices.
--
--   The paper's Theorem 1.3 (p. 3) reads: for every degree $d$, every $\varepsilon$ and all sufficiently large $n\ge n_0(d,\varepsilon)$ with $nd$ even, there is an explicit construction of an $(n,d,\lambda)$-graph with $\lambda\le2\sqrt{d-1}+\varepsilon$. Its proof starts from a graph $H$ on $n+u$ vertices, $u=o(n)$, supplied by Theorem 3.3 (Mohanty, O'Donnell and Paredes), with exactly properties 1–2 above, deletes $u$ vertices chosen by Lemma 3.1 and adds a matching on their neighbours. The statement above is that argument for an arbitrary input graph $H$ with the properties Theorem 3.3 provides, and for every number $u$ of deleted vertices that Lemma 3.1 can supply. Since $Nd$ is even for every $d$-regular graph on $N$ vertices, $(N-u)d$ is even exactly when $ud$ is even, which is the paper's condition "$nd$ is even" for $n = N - u$.
--
--   **Formalization Note** Theorem 3.3 is a cited input and is not formalized: its graph enters as the hypothesis $H$. The words "explicit" and "sufficiently large $n$", and "$u = o(n)$", are not formalized; condition 3 is the side condition of Lemma 3.1 and $u\le N/(2d^{2r+3})$ is the size Lemma 3.1 guarantees. The theorem says "every degree $d$", but its proof (Lemmas 3.1 and 3.2) requires $d\ge3$, which is assumed. The paper writes $r = \lceil 2/\varepsilon\rceil$, here $\lceil 2/\varepsilon\rceil_+$ as a natural number.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 3, Theorem 1.3; proof pp. 12–13 (relative to the graph supplied by Theorem 3.3)

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods

namespace ExplicitExpanders.Delete

/-- Theorem 1.3 (Alon, arXiv:2003.11673v1, p. 3), relative to the input graph supplied by
Theorem 3.3 ([18]): with `r = ⌈2/ε⌉`, a `d`-regular `(N, d, 2√(d-1) + ε/2)`-graph `H` in which
the `(2r+4)`-neighbourhood of every vertex contains at most one cycle and `r ≤ log_{d-1} N` yields,
for every `u ≤ N / (2 d^{2r+3})` with `ud` even, an `(N - u, d, 2√(d-1) + ε)`-graph. -/
theorem theorem_1_3 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (d : ℕ) (ε : ℝ) (hd : 3 ≤ d) (hε : 0 < ε)
    (hH : IsNDLambda H (Fintype.card V) d (2 * Real.sqrt ((d : ℝ) - 1) + ε / 2))
    (hcyc : ∀ v : V, AtMostOneCycleOn H (ball H v (2 * ⌈2 / ε⌉₊ + 4)))
    (hr : (⌈2 / ε⌉₊ : ℝ) ≤ Real.logb ((d : ℝ) - 1) (Fintype.card V))
    (u : ℕ) (hu : (u : ℝ) ≤ (Fintype.card V : ℝ) / (2 * (d : ℝ) ^ (2 * ⌈2 / ε⌉₊ + 3)))
    (heven : Even (u * d)) :
    ∃ G : SimpleGraph (Fin (Fintype.card V - u)),
      IsNDLambda G (Fintype.card V - u) d (2 * Real.sqrt ((d : ℝ) - 1) + ε) := by sorry

end ExplicitExpanders.Delete
