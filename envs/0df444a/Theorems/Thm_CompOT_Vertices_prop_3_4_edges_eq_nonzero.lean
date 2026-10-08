-- Prove2me | Theorems.Thm_CompOT_Vertices_prop_3_4_edges_eq_nonzero
-- name    : CompOT.Vertices.prop_3_4_edges_eq_nonzero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:03.262866+00:00
-- url     : https://prove2.me/theorems/cbb78a99-00c4-4454-87ed-0392ba9b0a84
-- title:
--   Proof of Proposition 3.4, p. 407 — for P ≥ 0 the edges of G(P) correspond to the nonzero entries of P
-- statement:
--   Let $P \in \mathbb R^{n\times m}$ have nonnegative entries (for instance $P \in U(a,b)$). Then the number of edges of the support graph $G(P) = (V\cup V', S(P))$ equals the number of nonzero entries of $P$:
--   $$|S(P)| = \#\{(i,j) : P_{ij} \ne 0\}.$$
--
--   Together with the forest edge bound this converts "$G(P)$ has no cycles" into "$P$ has at most $n+m-1$ nonzero entries".
--
--   **Formalization Note** Edges of $G(P)$ are undirected pairs $\{i, j'\}$ of the simple graph on `Fin n ⊕ Fin m`; the nonnegativity hypothesis is what makes $P_{ij} > 0$ and $P_{ij} \ne 0$ the same condition.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.4.1, end of the proof of Proposition 3.4, p. 407

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

namespace CompOT.Vertices

/-- End of the proof of Proposition 3.4, p. 407: for a matrix `P` with nonnegative entries
(in particular for `P ∈ U(a, b)`), the edges of the support graph `G(P)` are in bijection
with the nonzero entries of `P`, so `|S(P)|` equals the number of nonzero entries. -/
theorem prop_3_4_edges_eq_nonzero {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) :
    Nat.card (supportGraph P).edgeSet = (nonzeroEntries P).card := by sorry

end CompOT.Vertices
