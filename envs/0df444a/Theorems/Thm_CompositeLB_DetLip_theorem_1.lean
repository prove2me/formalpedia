-- Prove2me | Theorems.Thm_CompositeLB_DetLip_theorem_1
-- name    : CompositeLB.DetLip.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:30.394762+00:00
-- url     : https://prove2.me/theorems/5ee04f93-278b-4b61-b20b-a8871431163d
-- title:
--   Theorem 1, p. 5: deterministic gradient-and-prox algorithms need Ω(mLB/ε) queries
-- statement:
--   There are absolute constants $c,C>0$ with the following property. For every $m\ge2$, $L,B>0$, and $0<\varepsilon<LB/12$, there is a dimension $d\le C mLB/\varepsilon$ such that, for every deterministic algorithm querying an exact component-value, subgradient, and prox oracle, one can choose $m$ convex, $L$-Lipschitz functions on the radius-$B$ Euclidean ball and a valid oracle for them. If $x^*$ minimizes their average $F$ on that ball, then every query point $x_n$ among the first $c mLB/\varepsilon$ queries satisfies
--
--   $$F(x_n)-F(x^*)\ge\varepsilon.$$
--
--   The result bounds the oracle work needed to find an $\varepsilon$-suboptimal point for a nonsmooth finite sum, even when a component proximal point is available with every query.
--
--   **Formalization Note** The algorithm's candidate points are its query points, numbered from zero; its first query has count one. The dimension is selected before the algorithm, as the proof's construction permits. Proximal parameters are positive, and the oracle is a fixed, exact function of each query, valid even for points outside the ball. The hard function printed in (6) exceeds Lipschitz constant one for some parameters, so the Ω statement uses unspecified absolute constants and requires rescaling that construction.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Theorem 1, p. 5 (restated p. 11)

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

namespace CompositeLB.DetLip

/-- Theorem 1, pp. 5 and 11: the deterministic finite-sum gradient-and-prox oracle lower bound. -/
theorem theorem_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (m : ℕ) (L B ε : ℝ),
        2 ≤ m → 0 < L → 0 < B → 0 < ε → ε < L * B / 12 →
        ∃ d : ℕ, (d : ℝ) ≤ C * ((m : ℝ) * L * B / ε) ∧
          ∀ A : DetAlg m d,
            ∃ (f : Fin m → E d → ℝ) (O : Oracle m d),
              (∀ i : Fin m,
                ConvexOn ℝ (Metric.closedBall (0 : E d) B) (f i) ∧
                IsLipschitzOn L (f i) (Metric.closedBall (0 : E d) B)) ∧
              IsValidOracle f (Metric.closedBall (0 : E d) B) O ∧
              ∃ xstar ∈ Metric.closedBall (0 : E d) B,
                (∀ y ∈ Metric.closedBall (0 : E d) B,
                  avgF f xstar ≤ avgF f y) ∧
                ∀ n : ℕ,
                  (n : ℝ) + 1 ≤ c * ((m : ℝ) * L * B / ε) →
                    ε ≤ avgF f (query A O n).pt - avgF f xstar := by sorry

end CompositeLB.DetLip
