-- Prove2me | Theorems.Thm_BollobasChromatic_Main_packingNum_add_edge
-- name    : BollobasChromatic.Main.packingNum_add_edge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:07:12.185043+00:00
-- url     : https://prove2.me/theorems/c478e46c-3213-4832-b415-81de80ae1656
-- title:
--   Proof of Theorem 2, p. 51 — adding one edge increases the edge-disjoint K^r packing number X by at most one
-- statement:
--   Let $G$ be a graph on $[n]$, let $r\ge 0$, and let $uv$ be a pair of distinct vertices. Write $X(G)$ for the maximal number of pairwise edge-disjoint $K^r$ subgraphs of $G$, and $G+uv$ for $G$ with the edge $uv$ added. Then
--   $$
--   X(G)\;\le\;X(G+uv)\;\le\;X(G)+1 .
--   $$
--
--   In the proof of Theorem 2 this is the reason why the edge-exposure martingale $X_k=\mathbb E(X\mid E(G_p)\cap E_k)$ has differences $|X_{k+1}-X_k|\le 1$, which makes Lemma 1 applicable with $c=1$.
--
--   **Formalization Note** The page states only the upper bound ("increases $X$ by at most one"); the lower bound (monotonicity) is implicit in the two-sided claim $|X_{k+1}-X_k|\le 1$ and is stated as well. If $uv$ is already an edge both inequalities are trivial.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 51, proof of Theorem 2 (sentence before display (5))

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem packingNum_add_edge (n r : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n) (huv : u ≠ v) :
    packingNum G r ≤ packingNum (G ⊔ SimpleGraph.edge u v) r ∧
      packingNum (G ⊔ SimpleGraph.edge u v) r ≤ packingNum G r + 1 := by sorry

end BollobasChromatic.Main
