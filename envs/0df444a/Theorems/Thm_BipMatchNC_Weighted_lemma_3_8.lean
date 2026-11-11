-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_lemma_3_8
-- name    : BipMatchNC.Weighted.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:12:31.729506+00:00
-- url     : https://prove2.me/theorems/589e35ab-d616-436b-85b7-82522fd58cfb
-- title:
--   Lemma 3.8: for a feasible dual, a perfect matching of tight edges is maximum, has the dual value as weight, certifies optimality of the dual, and every maximum weight perfect matching is tight
-- statement:
--   Let $G$ be a balanced bipartite graph with left vertices $L$, right vertices $R$, edges $E$ and weights $w:E\to\mathbb N$, and let $(y,z)$, $y:L\to\mathbb R$, $z:R\to\mathbb R$, be a feasible dual solution: $y_u+z_v\ge w(u,v)$ for every edge. An edge is tight if $y_u+z_v=w(u,v)$. Suppose a perfect matching $M$ consists only of tight edges. Then
--
--   - $M$ is a maximum weight perfect matching of $G$;
--   - its weight equals the sum of all dual values: $$w(M)=\sum_{u\in L}y_u+\sum_{v\in R}z_v;$$
--   - $(y,z)$ is an optimal dual solution: its value is at most that of every feasible dual solution;
--   - every maximum weight perfect matching of $G$ consists only of tight edges.
--
--   This is complementary slackness for the bipartite matching LP. The paper applies it to $G$ and to the blow-up subgraphs $G^{r,\delta}[S]$ (Observation 3.11 and Claim 3.12).
--
--   Differences from the source:
--   - generalization: a feasible dual solution (y, z) of the dual LP, with z ≥ 0; 'the dual solution is optimal' → IsBalancedDualFeasible: y and z free; optimal among all such free duals; reason: p. 15: 'the dual constraint z_v ≥ 0 can be skipped in the case of a balanced bipartite graph'; every dual with z ≥ 0 is included, and optimality over the larger set implies optimality over the smaller one
--   - encoding: a balanced bipartite graph G with weight function w; perfect matchings → finite types L, R, edge indicator E : L → R → Bool, w : L → R → ℕ; a perfect matching is a bijection e : L ≃ R with every (u, e u) an edge; reason: general vertex sets; |L| = |R| is implied by the existence of e
--   - encoding: a perfect matching that consists only of tight edges → e : L ≃ R with IsTight E w y z u (e u) for all u (tightness includes being an edge); reason: the perfect-matching property follows from tightness, so it is not a separate hypothesis
--   - encoding: dual values → real numbers; weights natural numbers cast to ℝ; reason: the LP is over ℝ
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 16 (PDF 17), Lemma 3.8

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Bipartite

namespace BipMatchNC.Weighted

theorem lemma_3_8 {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : L → R → Bool) (w : L → R → ℕ) (y : L → ℝ) (z : R → ℝ)
    (hfeas : IsBalancedDualFeasible E w y z)
    (e : L ≃ R) (htight : ∀ u, IsTight E w y z u (e u)) :
    (IsPerfectMatchingOn E e ∧
        ∀ e' : L ≃ R, IsPerfectMatchingOn E e' → matchingWeight w e' ≤ matchingWeight w e) ∧
      (matchingWeight w e : ℝ) = dualValue y z ∧
      (∀ (y' : L → ℝ) (z' : R → ℝ), IsBalancedDualFeasible E w y' z' →
        dualValue y z ≤ dualValue y' z') ∧
      ∀ e' : L ≃ R, IsPerfectMatchingOn E e' →
        (∀ e'' : L ≃ R, IsPerfectMatchingOn E e'' → matchingWeight w e'' ≤ matchingWeight w e') →
        ∀ u, IsTight E w y z u (e' u) := by sorry

end BipMatchNC.Weighted
