-- Prove2me | Theorems.Thm_CellProbeTree_Matching_lemma_A_1
-- name    : CellProbeTree.Matching.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:35.543224+00:00
-- url     : https://prove2.me/theorems/78a27c61-6997-44e4-8449-6369f9b05465
-- title:
--   Lemma A.1 — exact Catalan convolution $F_u(b) = \frac{u}{2b+u}\binom{2b+u}{b}$
-- statement:
--   Let $F_u(b)$ be the number of ordered $u$-tuples of binary trees with total node size $b$; equivalently $F_u(b) = [z^b]\,C(z)^u = \sum_{b_1+\dots+b_u = b} \prod_i C_{b_i}$ (67). For $u \ge 1$ and $b \ge 0$,
--   $$F_u(b) = \frac{u}{2b+u}\binom{2b+u}{b}. \tag{68}$$
--   This is the count used for the uniform block source: $|\mathcal F_{\mathrm{block}}| = \binom{2u}{u}F_u(a)F_u(b)$.
--
--   Differences from the source:
--   - encoding: $F_u(b)$ → `forestCount u b`, the cardinality of the finite set of `Fin u → BinaryTree Unit` with total `numNodes` equal to $b$; the identity is stated in $\mathbb R$; reason: the paper's definition of $F_u(b)$ as a count of tuples of concrete binary trees (p. 19).
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 41, Appendix A.1, Lemma A.1, equations (67), (68)

import Mathlib
import Definitions.Def_CellProbeTree_Matching_LRBlock

namespace CellProbeTree.Matching

/-- Lemma A.1 (exact Catalan convolution): for `u ≥ 1` and `b ≥ 0`, the number `F_u(b)` of ordered
`u`-tuples of binary trees of total node size `b` is `u/(2b+u) · binom(2b+u, b)`. -/
theorem lemma_A_1 (u b : ℕ) (hu : 1 ≤ u) :
    (forestCount u b : ℝ) = (u : ℝ) / (2 * b + u) * (Nat.choose (2 * b + u) b : ℝ) := by sorry

end CellProbeTree.Matching
