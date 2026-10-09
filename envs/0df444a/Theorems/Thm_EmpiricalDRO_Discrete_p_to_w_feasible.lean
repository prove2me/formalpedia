-- Prove2me | Theorems.Thm_EmpiricalDRO_Discrete_p_to_w_feasible
-- name    : EmpiricalDRO.Discrete.p_to_w_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:50.176971+00:00
-- url     : https://prove2.me/theorems/4614306a-ee57-41e1-9503-62fcf199ed63
-- title:
--   Proposition 1, proof p. 24 — from support weights to sample weights
-- statement:
--   Let $n>0$ observations be classified among $k$ support points, with $n_i$ observations in class $i$ and empirical proportion $\hat p_i=n_i/n$. Let $a_i$ be any real loss at point $i$. If a support probability vector $p$ belongs to the finite-support Burg ball of radius $\eta$, assign every observation $j$ in class $i$ the weight $w_j=p_i/n_i$. Then
--
--   $$
--   w\in\mathcal U_n(\eta),\qquad \sum_{j=1}^n w_j a_{c(j)}=\sum_{i=1}^k p_i a_i.
--   $$
--
--   This is one direction of the reduction from the support optimization to the empirical optimization, preserving both feasibility and objective value.
--
--   **Formalization Note** Empty classes receive no sample weights. The source proves the claim at $\eta=\chi^2_{1,1-\alpha}/(2n)$; the same deterministic argument holds for every real $\eta$. The finite-support ball carries the absolute-continuity and positive-mass conventions stated in its definition.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 24, proof of Proposition 1, paragraph beginning ‘To this end’

import Mathlib
import Definitions.Def_EmpiricalDRO_Discrete_Setting

namespace EmpiricalDRO.Discrete

/-- Proof of Proposition 1, p. 24: distribute each support mass equally among the
observations in its class; feasibility and the objective value are preserved. -/
theorem p_to_w_feasible {n k : ℕ} (hn : 0 < n) (c : Fin n → Fin k)
    (a : Fin k → ℝ) (η : ℝ) (p : Fin k → ℝ)
    (hp : p ∈ burgBall (phat c) η) :
    let w : Fin n → ℝ := fun j => p (c j) / (count c (c j) : ℝ)
    w ∈ PhiDivRobust.Counterpart.probUncertaintySet EmpiricalDRO.Coverage.burg
      (fun _ => (1 : ℝ) / n) η ∧
    ∑ j, w j * a (c j) = ∑ i, p i * a i := by sorry

end EmpiricalDRO.Discrete
