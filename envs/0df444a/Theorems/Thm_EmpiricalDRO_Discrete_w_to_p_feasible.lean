-- Prove2me | Theorems.Thm_EmpiricalDRO_Discrete_w_to_p_feasible
-- name    : EmpiricalDRO.Discrete.w_to_p_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:07:04.713479+00:00
-- url     : https://prove2.me/theorems/b35e0ac8-f577-4602-a52a-baf6274f1069
-- title:
--   Proposition 1, proof p. 24 — from sample weights to support weights
-- statement:
--   Let $n>0$ observations be classified among $k$ support points, with empirical proportions $\hat p_i=n_i/n$, and let $a_i$ be any real loss at point $i$. For a feasible weight vector $w$ in the empirical Burg ball $\mathcal U_n(\eta)$, aggregate the weights within each class: $p_i=\sum_{j:c(j)=i}w_j$. Then
--
--   $$
--   p\in\mathcal U'_{\mathrm{Burg}}(\eta),\qquad \sum_{i=1}^k p_i a_i=\sum_{j=1}^n w_j a_{c(j)}.
--   $$
--
--   This is the reverse reduction. Jensen's inequality bounds the divergence of the aggregated vector, while aggregation preserves its objective value.
--
--   **Formalization Note** The source uses radius $\chi^2_{1,1-\alpha}/(2n)$; the statement allows any real $\eta$. The finite-support ball enforces zero mass at unobserved support points and positive mass at observed points.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 24, proof of Proposition 1, paragraph beginning ‘On the other hand’

import Mathlib
import Definitions.Def_EmpiricalDRO_Discrete_Setting

namespace EmpiricalDRO.Discrete

/-- Proof of Proposition 1, p. 24: aggregate observation weights by support point;
Jensen's inequality gives feasibility and the objective value is preserved. -/
theorem w_to_p_feasible {n k : ℕ} (hn : 0 < n) (c : Fin n → Fin k)
    (a : Fin k → ℝ) (η : ℝ) (w : Fin n → ℝ)
    (hw : w ∈ PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg
      (fun _ => (1 : ℝ) / n) η) :
    let p : Fin k → ℝ := fun i =>
      ∑ j ∈ Finset.univ.filter (fun j => c j = i), w j
    p ∈ burgBall (phat c) η ∧
    ∑ i, p i * a i = ∑ j, w j * a (c j) := by sorry

end EmpiricalDRO.Discrete
