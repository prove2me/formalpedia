-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_lemma_3
-- name    : FinDisclosure.Threshold.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:22.419129+00:00
-- url     : https://prove2.me/theorems/a2624d68-ca28-4794-a9be-602c893e0b28
-- title:
--   Lemma 3, p. 35 — at an optimum of (31) the mass and financing constraints are not both slack (with λI ≤ B)
-- statement:
--   Assume the standing assumptions of the model and $\lambda I \le B$. Fix $q \in (0,1)$ and let $\mu_h$ be an optimal solution of the relaxed problem (31), that is, $\mu_h$ is feasible for (31) and
--   $$q\int_0^1 g(s)\,\mu_h(s)\,ds \;\ge\; q\int_0^1 g(s)\,m(s)\,ds \quad\text{for every } m \text{ feasible for (31)},$$
--   where $g(s) = s - c(s) + B + \lambda(c(s) - I)$. Then the constraints $\int_0^1 \mu_h(s)\,ds \le 1$ and $\int_0^1 \mu_h(s) c(s)\,ds \ge I$ cannot both be slack:
--   $$\int_0^1 \mu_h(s)\,ds = 1 \quad\text{or}\quad \int_0^1 c(s)\mu_h(s)\,ds = I.$$
--
--   In the paper this is the step that fixes the dual multipliers and gives the optimal dual value (35).
--
--   **Formalization Note** The hypothesis $\lambda I \le B$ is not in the paper, and the lemma is false without it. Take $\mu_0 = 1$ on $[0,1]$, $c(s) = s$, $I = 0.6$, $B = 0.1$, $\lambda = 1$ and $q = 0.55$. Then $\mu_h = \mu_0/q$ on $[0.5,1]$ is optimal for (31), with $\int\mu_h \approx 0.909$ and $\int c\,\mu_h \approx 0.682 > 0.6$, so both constraints are slack. Under $\lambda I \le B$ the integrand $g$ is nonnegative on $[0,1]$. The lemma is posed on the primal problem (31), which is what its sentence says; the paper places it inside the dual argument.
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 35 (PDF 35), Lemma 3; problem (31), p. 34

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Lemma 3, p. 35 (with the added hypothesis `λ I ≤ B`): at an optimal solution `mh` of the relaxed
problem (31) with `q ∈ (0, 1)`, the mass constraint `∫_0^1 µh ≤ 1` and the financing constraint
`∫_0^1 µh c ≥ I` cannot both be slack. -/
theorem lemma_3 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam) (hB : lam * I ≤ B)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (mh : ℝ → ℝ) (hmh : Feas31 c f0 I q mh)
    (hopt : ∀ m : ℝ → ℝ, Feas31 c f0 I q m → obj c I B lam q m ≤ obj c I B lam q mh) :
    ∫ s in (0:ℝ)..1, mh s = 1 ∨ ∫ s in (0:ℝ)..1, c s * mh s = I := by sorry

end FinDisclosure.Threshold
