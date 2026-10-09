-- Prove2me | Theorems.Thm_CompositeLB_DetSC_theorem_4
-- name    : CompositeLB.DetSC.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:48.682675+00:00
-- url     : https://prove2.me/theorems/8ef8560a-3d34-496f-9219-8760b9e800da
-- title:
--   Theorem 4, p. 6 — deterministic smooth strongly convex finite-sum oracle lower bound
-- statement:
--   There are absolute constants $c,C>0$ with the following property. For every $m\ge2$, $\gamma,\lambda,\epsilon>0$ with $\gamma/\lambda>73$, and $\epsilon_0>3\gamma\epsilon/\lambda$, set $R=m\sqrt{\gamma/\lambda}\log(\lambda\epsilon_0/(\gamma\epsilon))$. Some dimension $d\le CR$ works for every deterministic algorithm $A$ using exact component value, gradient, and prox queries: after seeing $A$, there are $m$ globally $\gamma$-smooth and $\lambda$-strongly convex components $f_i$, with a consistent exact oracle, whose average $F$ has a global minimizer $x^*$, $F(0)-F(x^*)=\epsilon_0$, and every query point $x_n$ with $n+1\le cR$ obeys
--
--   $$F(x_n)-F(x^*)\ge\epsilon.$$
--
--   Thus an algorithm needs order $m\sqrt{\gamma/\lambda}\log(\lambda\epsilon_0/(\gamma\epsilon))$ oracle queries to find an $\epsilon$-suboptimal point in this class.
--
--   **Formalization Note** The hidden constants precede all parameters. The dimension is chosen before $A$, as supported by the construction. The domain is all of $\mathbb R^d$, a choice allowed by the paper's $X\subseteq\mathbb R^d$. Query $n$ is numbered from zero, and the point $\hat x$ of the page ranges over the algorithm's query points. The oracle is exact and memoryless and requires positive prox parameters. Mathlib's StrongConvexOn uses the equivalent chord inequality for differentiable functions.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Theorem 4, p. 6 (restated App. B.4, p. 16)

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Model

namespace CompositeLB.DetSC

/-- Woodworth--Srebro, Theorem 4: a deterministic smooth strongly convex
finite-sum oracle lower bound, with absolute constants placed before the parameters.
`lam` is λ, `gamma` is γ, `eps0` is ε₀. The dimension `d` is chosen before the algorithm,
the domain is all of ℝ^d, and `query A O n` is the paper's `(n+1)`-st CompositeLB.DetLip.query. -/
theorem theorem_4 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (m : ℕ) (gamma lam eps eps0 : ℝ),
        2 ≤ m → 0 < gamma → 0 < lam → 73 < gamma / lam →
        0 < eps → 3 * gamma * eps / lam < eps0 →
        ∃ d : ℕ,
          (d : ℝ) ≤ C * ((m : ℝ) * Real.sqrt (gamma / lam) *
            Real.log (lam * eps0 / (gamma * eps))) ∧
          ∀ A : CompositeLB.DetLip.DetAlg m d,
            ∃ (f : Fin m → CompositeLB.DetLip.E d → ℝ) (O : CompositeLB.DetLip.Oracle m d),
              (∀ i : Fin m,
                CompositeLB.DetSmooth.IsSmoothOn gamma (f i) Set.univ ∧
                  StrongConvexOn Set.univ lam (f i)) ∧
              CompositeLB.DetSmooth.IsValidOracle f Set.univ O ∧
              ∃ xstar : CompositeLB.DetLip.E d,
                (∀ y : CompositeLB.DetLip.E d, CompositeLB.DetLip.avgF f xstar ≤ CompositeLB.DetLip.avgF f y) ∧
                CompositeLB.DetLip.avgF f 0 - CompositeLB.DetLip.avgF f xstar = eps0 ∧
                ∀ n : ℕ,
                  (n : ℝ) + 1 ≤ c * ((m : ℝ) * Real.sqrt (gamma / lam) *
                    Real.log (lam * eps0 / (gamma * eps))) →
                  eps ≤ CompositeLB.DetLip.avgF f (CompositeLB.DetLip.query A O n).pt - CompositeLB.DetLip.avgF f xstar := by sorry

end CompositeLB.DetSC
