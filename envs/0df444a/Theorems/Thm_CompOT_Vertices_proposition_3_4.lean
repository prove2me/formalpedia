-- Prove2me | Theorems.Thm_CompOT_Vertices_proposition_3_4
-- name    : CompOT.Vertices.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:48.293463+00:00
-- url     : https://prove2.me/theorems/9ef7ee75-0891-43d7-86a5-0a2ea816da03
-- title:
--   Proposition 3.4, p. 406 — the support graph of an extremal point of U(a, b) has no cycles; P has at most n + m − 1 nonzero entries
-- statement:
--   **Proposition 3.4 (Extremal solutions).** Let $a \in \Sigma_n$, $b \in \Sigma_m$ be histograms, and let $P$ be an extremal point of the transportation polytope
--   $$U(a,b) = \{P \in \mathbb R_+^{n\times m} : P\mathbb 1_m = a,\ P^\top\mathbb 1_n = b\}.$$
--   Let $S(P)$ be the set of edges $(i, j')$, $i \in [\![n]\!]$, $j \in [\![m]\!]$, with $P_{ij} > 0$. Then the graph $G(P) = (V \cup V', S(P))$ on the $n + m$ nodes $V = \{1,\dots,n\}$, $V' = \{1',\dots,m'\}$ has no cycles. In particular,
--   $$\#\{(i,j) : P_{ij} \ne 0\} \le n + m - 1 .$$
--
--   The vertices of $U(a,b)$ are therefore sparse: their supports are forests of the complete bipartite graph between sources and targets. Since a linear program over $U(a,b)$ attains its minimum at a vertex, optimal transport plans can be sought among such sparse matrices; this is the structure exploited by the network simplex and the north-west corner rule.
--
--   **Formalization Note** Indices are `Fin n`, `Fin m`. Extremality is the book's midpoint definition relative to $U(a,b)$. "No cycles" is `SimpleGraph.IsAcyclic` of the undirected bipartite support graph. The simplex hypotheses come from the book's standing notation (p. 360) and imply nonempty index sets. Thus natural-number subtraction in $n+m-1$ agrees with the book's integer expression.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.4.1, Proposition 3.4, p. 406

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

namespace CompOT.Vertices

/-- Proposition 3.4 (Extremal solutions), p. 406: for the book's histograms
`a ∈ Σₙ`, `b ∈ Σₘ` (Notation, p. 360), if `P` is an extremal point of `U(a, b)`,
then its support graph has no cycles and `P` has at most `n + m − 1` nonzero entries. -/
theorem proposition_3_4 {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (hP : IsExtremal (CompOT.Assignment.couplings a b) P) :
    (supportGraph P).IsAcyclic ∧ (nonzeroEntries P).card ≤ n + m - 1 := by sorry

end CompOT.Vertices
