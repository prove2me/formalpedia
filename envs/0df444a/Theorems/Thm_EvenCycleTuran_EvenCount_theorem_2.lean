-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_theorem_2
-- name    : EvenCycleTuran.EvenCount.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:49.915105+00:00
-- url     : https://prove2.me/theorems/06ec184d-0296-44f9-98ed-e8d60e27df81
-- title:
--   Theorem 2 (Erdős–Gallai), p. 2 — a graph with no cycle longer than k has at most k(n−1)/2 edges (corrected)
-- statement:
--   Let $k\ge2$ and let $G$ be a graph on $n$ vertices that contains no cycle of length greater than $k$. Then
--   $$|E(G)|\le\frac{k(n-1)}{2}.$$
--
--   This is the Erdős–Gallai bound on the number of edges of a graph of circumference at most $k$. In the paper it is the input to Claim 1, applied to the edges inside and next to the neighbourhood of a vertex of a $C_{2k}$-free graph.
--
--   **Formalization Note** The paper prints the bound as $(k-1)n/2$, which is false: two triangles sharing a vertex ($k=3$, $n=5$) have $6>5$ edges. The statement here is the bound Erdős and Gallai proved; Claim 1 needs only $|E|\le(k-1)n$ for circumference $2k-2$, which the corrected bound gives. The hypothesis $k\ge2$ is added: for $k\le1$ "no cycle longer than $k$" means a forest, which may have $n-1>k(n-1)/2$ edges. The bound is stated as $2|E(G)|\le k(n-1)$ in $\mathbb N$ (at $n=0$ both sides are $0$).
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 2, Theorem 2 (Erdős, Gallai [10]); corrected bound k(n−1)/2 (the page prints (k−1)n/2)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph

theorem theorem_2 (n k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ a : ℕ, k < a → (cycleGraph a).Free G) :
    2 * #G.edgeFinset ≤ k * (n - 1) := by sorry

end EvenCycleTuran.EvenCount
