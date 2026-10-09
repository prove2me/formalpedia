-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_theorem_3
-- name    : CompositeLB.DetSmooth.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:02.023214+00:00
-- url     : https://prove2.me/theorems/a199c906-7a1c-4749-8a59-0f1bdf7ea405
-- title:
--   Theorem 3, p. 6 — Ω(m√(γB²/ε)) deterministic gradient and prox oracle lower bound
-- statement:
--   Let $m\ge2$ and $\gamma,B,\epsilon>0$. For some absolute positive constants $c,C$, there is a dimension $d\le C m\sqrt{\gamma B^2/\epsilon}$ such that for every deterministic algorithm $A$ querying component values, gradients, and exact proximal points, one can choose $m$ convex $\gamma$-smooth components on the closed $B$-ball, an exact oracle, and a minimizer $x^*$ for their average $F$ over the ball, with every one of the first $\lfloor c m\sqrt{\gamma B^2/\epsilon}\rfloor$ query points satisfying
--
--   $$F(x_n)-F(x^*)\ge\epsilon.$$
--
--   Hence an algorithm needs order $m\sqrt{\gamma B^2/\epsilon}$ component-oracle queries to obtain a strictly $\epsilon$-suboptimal point. The constants are independent of $m,\gamma,B,\epsilon$ and of the algorithm.
--
--   **Formalization Note** The dimension is chosen before $A$, as the paper's construction allows. The oracle is a fixed exact function of each query and takes $\beta>0$; query points may lie outside the ball. The early points are those submitted to the oracle, indexed from zero; an algorithm can query any proposed output point. The printed final numeric count on p. 15 is false for some parameters, so the theorem retains absolute constants rather than asserting that count.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Theorem 3, p. 6 (restated Appendix B.3, p. 14)

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Model

namespace CompositeLB.DetSmooth

/-- Theorem 3, p. 6: an absolute-constant deterministic lower bound for
finite sums of convex smooth components with exact gradient and prox access. -/
theorem theorem_3 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (m : ℕ) (γ B ε : ℝ), 2 ≤ m → 0 < γ → 0 < B → 0 < ε →
        ∃ d : ℕ,
          (d : ℝ) ≤ C * ((m : ℝ) * Real.sqrt (γ * B ^ 2 / ε)) ∧
          ∀ A : CompositeLB.DetLip.DetAlg m d,
            ∃ (f : Fin m → CompositeLB.DetLip.E d → ℝ) (O : CompositeLB.DetLip.Oracle m d),
              (∀ i, ConvexOn ℝ (Metric.closedBall (0 : CompositeLB.DetLip.E d) B) (f i) ∧
                IsSmoothOn γ (f i) (Metric.closedBall (0 : CompositeLB.DetLip.E d) B)) ∧
              IsValidOracle f (Metric.closedBall (0 : CompositeLB.DetLip.E d) B) O ∧
              ∃ xstar ∈ Metric.closedBall (0 : CompositeLB.DetLip.E d) B,
                (∀ y ∈ Metric.closedBall (0 : CompositeLB.DetLip.E d) B,
                  CompositeLB.DetLip.avgF f xstar ≤ CompositeLB.DetLip.avgF f y) ∧
                ∀ n : ℕ,
                  (n : ℝ) + 1 ≤ c * ((m : ℝ) * Real.sqrt (γ * B ^ 2 / ε)) →
                    ε ≤ CompositeLB.DetLip.avgF f (CompositeLB.DetLip.query A O n).pt - CompositeLB.DetLip.avgF f xstar := by sorry

end CompositeLB.DetSmooth
