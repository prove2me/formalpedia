-- Prove2me | Theorems.Thm_FairPricingPerturbation_feasible_curve
-- name    : FairPricingPerturbation.feasible_curve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:17.514509+00:00
-- url     : https://prove2.me/theorems/12583bd8-fc23-4837-be3a-9cd25fbc2a45
-- title:
--   Feasible prices along a first-order direction
-- statement:
--   Let $M_0,M_1:\mathbb R\to\mathbb R$ be continuous on a neighbourhood of $b_0>0$ and $b_1>0$ respectively, differentiable there with $M_i'(b_i)=m_i$, and suppose $(m_0,m_1)\ne(0,0)$. Write $\Delta=M_0(b_0)-M_1(b_1)$ and let $v\in\mathbb R^2$ satisfy the linearised binding constraint
--   $$m_0v_0-m_1v_1=-\Delta .$$
--   Then for every $\tau>0$ there is $\varepsilon>0$ such that for all $\alpha\in(0,\varepsilon]$ there exist prices $q\ge0$ with
--   $$|M_0(q_0)-M_1(q_1)|\le(1-\alpha)|\Delta|\qquad\text{and}\qquad |q_i-b_i-\alpha v_i|\le\tau\alpha\ (i=0,1).$$
--
--   In words: a direction that satisfies the fairness constraint to first order can be followed by genuinely feasible prices up to an $o(\alpha)$ error. It isolates one step of the proof of Lemma 1 (Online Appendix A, pp. 31–33).
--
--   **Formalization Note.** Pure real analysis; the two fairness measures are arbitrary real functions.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; auxiliary lemma for the proof of Lemma 1, Online Appendix A, pp. 31-33 (construction of feasible perturbations, cf. Eqs. (5)-(7)).

import Mathlib

open Filter Topology Asymptotics

namespace FairPricingPerturbation

theorem feasible_curve
    (M : Fin 2 → ℝ → ℝ) (b mm v : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (M i) (Set.Icc (b i - η) (b i + η)))
    (hMd : ∀ i, HasDerivAt (M i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hv : mm 0 * v 0 - mm 1 * v 1 = -(M 0 (b 0) - M 1 (b 1))) :
    ∀ τ > 0, ∃ ε > 0, ∀ α ∈ Set.Ioc (0 : ℝ) ε, ∃ q : Fin 2 → ℝ,
      (∀ i, 0 ≤ q i) ∧
      |M 0 (q 0) - M 1 (q 1)| ≤ (1 - α) * |M 0 (b 0) - M 1 (b 1)| ∧
      ∀ i, |q i - b i - α * v i| ≤ τ * α := by sorry

end FairPricingPerturbation
