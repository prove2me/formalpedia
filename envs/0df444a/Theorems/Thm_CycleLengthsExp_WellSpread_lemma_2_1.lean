-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_lemma_2_1
-- name    : CycleLengthsExp.WellSpread.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:12.449014+00:00
-- url     : https://prove2.me/theorems/729acad4-5701-41e7-9522-0ec64f47f94d
-- title:
--   Lemma 2.1 (In particular), p. 4 — components of a (δn,α)-expander have diameter at most (7/(δα)) log n
-- statement:
--   Let $0<\delta<1$ and $0<\alpha\le1$, and let $G$ be a $(\delta n,\alpha)$-expander on $n$ vertices. Then any two vertices $u,v$ in the same connected component of $G$ satisfy
--
--   $$\operatorname{dist}_G(u,v)\ \le\ \frac{7}{\delta\alpha}\,\log_2 n.$$
--
--   Equivalently, every connected component $C$ of $G$ induces a graph $G[C]$ of diameter at most $\frac{7}{\delta\alpha}\log_2 n$. It bounds the depth of breadth-first trees in the proofs of Lemma 2.7 and Theorem 1.
--
--   **Formalization Note.** The diameter of $G[C]$ is expressed through distances between vertices of the same component: shortest paths between two vertices of $C$ stay in $C$, so $\operatorname{dist}_{G[C]}=\operatorname{dist}_G$ on $C$. The first inequality of Lemma 2.1, $\operatorname{diam}(G[C])<(\lceil n/k\rceil-1)(2\lceil\log k/\log(1+\alpha)\rceil+1)$, is not stated: it fails as printed for the path $P_n$ with $k=1$.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 4, Lemma 2.1, second sentence ("In particular, if k = δn ...")

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem lemma_2_1 (n : ℕ) (G : SimpleGraph (Fin n)) (δ α : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hG : IsKAlphaExpander (δ * n) α G) (u v : Fin n) (huv : G.Reachable u v) :
    (G.dist u v : ℝ) ≤ 7 / (δ * α) * Real.logb 2 n := by sorry

end CycleLengthsExp.WellSpread
