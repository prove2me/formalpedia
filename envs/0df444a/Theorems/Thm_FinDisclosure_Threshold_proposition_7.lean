-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_proposition_7
-- name    : FinDisclosure.Threshold.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:35.490759+00:00
-- url     : https://prove2.me/theorems/c7574c94-076d-44f9-b7d0-f4dc72355aaf
-- title:
--   Proposition 7, p. 33 — for fixed q ∈ (0,1), if (30) is feasible, the threshold density (17) with Ŝ = [ŝ, 1] is optimal
-- statement:
--   Assume the standing assumptions of the model. Fix $q \in (0,1)$ and let $t \in [0,1]$ be the cutoff with
--   $$\int_t^1 \mu_0(s)\,ds = q.$$
--   Suppose problem (30) is feasible, i.e. some density satisfies the financing condition (14), the Bayes plausibility constraint (13), the mass conditions and nonnegativity. Then the threshold density
--   $$\mu_h(s) = \begin{cases} \mu_0(s)/q & s \ge t,\\ 0 & \text{otherwise}\end{cases}$$
--   of (17), with $\hat S = [t,1]$, is feasible for (30), and it is optimal:
--   $$q\int_0^1 g(s)\,m(s)\,ds \;\le\; q\int_0^1 g(s)\,\mu_h(s)\,ds \quad\text{for every } m \text{ feasible for (30)},$$
--   where $g(s) = s - c(s) + B + \lambda(c(s) - I)$.
--
--   This is the characterization of the optimal policy for a fixed probability $q$ of financing, the first half of the proof of Proposition 1.
--
--   **Formalization Note** The paper assumes that (30) "has a solution". Here only feasibility is assumed, which makes the statement stronger, and it remains true. "The optimal policy is given by (17)" is read as "(17) is an optimal solution": optimal solutions need not be unique, for instance when $\lambda = 0$ and $c(s) = s$ on an interval, where $g$ is constant. The equicontinuity restriction (32) is not imposed. No hypothesis $\lambda I \le B$ is needed.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 33 (PDF 33), Proposition 7; (17), p. 17 (PDF 17)

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Proposition 7, p. 33: for `q ∈ (0, 1)`, if problem (30) is feasible, then the threshold density
(17) with `Ŝ = [t, 1]`, where `∫_t^1 µ0 = q`, is feasible and optimal for (30). -/
theorem proposition_7 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (htq : ∫ s in t..1, f0 s = q) (hfeas : ∃ m : ℝ → ℝ, Feas30 c f0 I q m) :
    Feas30 c f0 I q (thresholdDensity f0 q t) ∧
      ∀ m : ℝ → ℝ, Feas30 c f0 I q m →
        obj c I B lam q m ≤ obj c I B lam q (thresholdDensity f0 q t) := by sorry

end FinDisclosure.Threshold
