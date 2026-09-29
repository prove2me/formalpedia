-- Prove2me | Theorems.Thm_DistInterpRO_Equivalence_dual_bound
-- name    : DistInterpRO.Equivalence.dual_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:44:49.00396+00:00
-- url     : https://prove2.me/theorems/074980dd-a317-476f-8ee0-777bce558a03
-- title:
--   Weak duality: every dual feasible $\alpha$ has objective at most $\sum_i c_i f_i$
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ be measurable, let $c_1,\dots,c_n>0$ with $\sum_i c_i=1$, and let $\mathcal Z_1,\dots,\mathcal Z_n\subseteq\mathbb R^m$ be nonempty Borel sets on each of which $f$ is bounded below. Put $f_i=\inf_{x\in\mathcal Z_i}f(x)$ and $N=[1:n]$. Then for every dual feasible $\alpha\in\mathbb R^{2^n}$ (in the sense of the dual problem of Theorem 2.1: $\sum_S\alpha_S\mathbf 1(x\in\mathcal Z_S)\le f(x)$ on $\mathcal Z_N$ and $\alpha_S\ge 0$ for $S\ne N$),
--   $$\sum_{i\in N}c_i\sum_{S\subseteq N}\alpha_S\,\mathbf 1(i\in S)\ \le\ \sum_{i\in N}c_i f_i.$$
--
--   This is one half of the statement that the optimal value of the dual problem equals $\sum_i c_i f_i$, which by strong duality gives Eq. (4).
--
--   **Formalization Note** The hypothesis that $f$ is bounded below on each $\mathcal Z_i$ is the proof's standing reduction ("we can assume without loss of generality that $\inf_{x_i\in\mathcal Z_i}f(x_i)>-\infty$"); it makes $f_i$ a real number, computed as the real infimum `⨅ x : Z i, f x` over a nonempty set bounded below. No sign condition is placed on $\alpha_N$.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 97, proof of Theorem 2.1, paragraph after 'Therefore, it suffices to show'

import Mathlib
import Definitions.Def_DistInterpRO_Equivalence_Model

open MeasureTheory

namespace DistInterpRO.Equivalence

theorem dual_bound {m n : ℕ} (f : (Fin m → ℝ) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (hsum : ∑ i, c i = 1)
    (Z : Fin n → Set (Fin m → ℝ)) (hZne : ∀ i, (Z i).Nonempty)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hbdd : ∀ i, BddBelow (f '' Z i))
    (α : Finset (Fin n) → ℝ) (hα : IsDualFeasible Z f α) :
    ∑ i, c i * ∑ S : Finset (Fin n), α S * (if i ∈ S then (1 : ℝ) else 0) ≤
      ∑ i, c i * ⨅ x : Z i, f x := by sorry

end DistInterpRO.Equivalence
