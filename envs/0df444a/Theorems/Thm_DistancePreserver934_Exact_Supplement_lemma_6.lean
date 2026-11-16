-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_lemma_6
-- name    : DistancePreserver934.Exact.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:22:57.644209+00:00
-- url     : https://prove2.me/theorems/d3e2dad3-02ce-4880-895f-dc1483dc8bab
-- title:
--   Lemma 6 — A large edge-disjoint demand batch covered by few nearby vertices
-- statement:
--   In the same §4 minimal-preserver setting with a fixed edge-disjoint shortest-path family, let the real parameters satisfy $1\le r\le d$. Assume the actual average degree $2|E(H)|/n$ is at least $d$, and every path has length at least $r$. There is an absolute constant $c>0$ and sets $Q\subseteq P$, $S\subseteq V$ for which $S$ covers $Q$ and
--
--   $$|Q|\ge cd^2r,\qquad |S|\le 16|Q|/d,\qquad\operatorname{diam}_H(S)\le4r.$$
--
--   All $n$ ambient vertices, including isolated ones, contribute to the average degree. On an empty type that real quotient is zero, so the positive degree premise cannot hold. This is the simultaneous batch-and-cover guarantee supporting Theorem 5.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
--   - encoding: O(|Q|/d) covering-set size → the explicit upper bound 16|Q|/d; reason: the source proof on printed p. 13 derives this coefficient for the same Q and S
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Lemma 6, printed p. 10 (PDF p. 11)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem lemma_6 :

  ∃ c : ℝ, 0 < c ∧ ∀ {V : Type} [Fintype V]
    (G H : SimpleGraph V) (P : Finset (Sym2 V))
    (π : EdgeDisjointFamily H P) (d r : ℝ),
    IsDemandSet G P → IsMinimalPreserver G H P →
    (2 * (numEdges H : ℝ) / (Fintype.card V : ℝ) ≥ d) →
    (∀ q : P, r ≤ ((π.path q).walk.length : ℝ)) →
    1 ≤ r → r ≤ d →
    ∃ (Q : Finset (Sym2 V)) (S : Finset V),
      Q ⊆ P ∧ Covers H S Q ∧ c * d ^ 2 * r ≤ (Q.card : ℝ) ∧
      (S.card : ℝ) ≤ 16 * (Q.card : ℝ) / d ∧ DiamLE H S (4 * r)
 := by sorry

end DistancePreserver934.Exact.Supplement
