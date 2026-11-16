-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_lemma_7
-- name    : DistancePreserver934.Exact.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:22:12.809304+00:00
-- url     : https://prove2.me/theorems/2547580d-4596-4b88-8495-8a25a42b2656
-- title:
--   Lemma 7 — Quadratic growth of H-balls in the edge-disjoint setting
-- statement:
--   Let $H$ be an inclusion-minimal preserver of a set $P$ of distinct, reachable unordered demands in $G$, and fix mutually edge-disjoint $H$-shortest walks $\pi(q)$. There is an absolute $c>0$ such that, for real $1\le r\le d$, if every chosen walk has length at least $r$ and an auxiliary subgraph $H_C=(V^*,E_C)\subseteq H$ has minimum degree at least $d/4$, then
--
--   $$|B_H(u,r)|\ge cdr^2\qquad(u\in V^*).$$
--
--   The ball metric is that of unchanged $H$, not the auxiliary core. The core is encoded by a graph on the ambient type with all its edges supported on $V^*$. An empty core is permitted. This supplies the growth estimate used by Lemma 6.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Lemma 7, printed p. 11 (PDF p. 12)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem lemma_7 :

  ∃ c : ℝ, 0 < c ∧ ∀ {V : Type} [Fintype V]
    (G H : SimpleGraph V) (P : Finset (Sym2 V))
    (π : EdgeDisjointFamily H P) (d r : ℝ)
    (K : SimpleGraph V) (C : Finset V),
    IsDemandSet G P → IsMinimalPreserver G H P →
    (∀ q : P, r ≤ ((π.path q).walk.length : ℝ)) →
    1 ≤ r → r ≤ d → K ≤ H →
    (∀ v w : V, K.Adj v w → v ∈ C ∧ w ∈ C) →
    (∀ u ∈ C, d / 4 ≤ (Nat.card {v : V // K.Adj u v} : ℝ)) →
    ∀ u ∈ C, c * d * r ^ 2 ≤ ((ball H u r).card : ℝ)
 := by sorry

end DistancePreserver934.Exact.Supplement
