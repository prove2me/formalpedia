-- Prove2me | Theorems.Thm_EmpiricalDRO_Discrete_proposition1_discrete_reduction
-- name    : EmpiricalDRO.Discrete.proposition1_discrete_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:22.653266+00:00
-- url     : https://prove2.me/theorems/5f19ba76-3786-4c89-8e35-f2b3fbd78b73
-- title:
--   Proposition 1, p. 11 — empirical and finite-support Burg DRO values coincide
-- statement:
--   Fix a decision $x$ and a loss $h(x;s_i)$ at each of $k$ support points. A sample of size $n>0$ assigns each observation to one of those points. Let $\hat p_i=n_i/n$ be its histogram and let $\kappa\ge0$. Use the empirical Burg ball $\mathcal U_n(\kappa/(2n))$ for weights on the observations and the finite-support Burg ball $\mathcal U'_{\mathrm{Burg}}(\kappa/(2n))$ for weights on the support. Then both optimal values agree:
--
--   $$
--   \min_{w\in\mathcal U_n(\kappa/(2n))}\sum_{j=1}^n w_j h(x;s_{c(j)})
--   =\min_{p\in\mathcal U'_{\mathrm{Burg}}(\kappa/(2n))}\sum_{i=1}^k p_i h(x;s_i),
--   $$
--   $$
--   \max_{w\in\mathcal U_n(\kappa/(2n))}\sum_{j=1}^n w_j h(x;s_{c(j)})
--   =\max_{p\in\mathcal U'_{\mathrm{Burg}}(\kappa/(2n))}\sum_{i=1}^k p_i h(x;s_i).
--   $$
--
--   Proposition 1 identifies the empirical DRO with the ordinary Burg-divergence DRO on the observed finite support; the printed choice is $\kappa=\chi^2_{1,1-\alpha}$.
--
--   **Formalization Note** The source fixes $x\in\Theta$; Lean takes an arbitrary fixed $x$, a generalization. The paper's displayed (28) omits the absolute-continuity clause from (13)–(14); the formalized support ball includes it. The parameter $\kappa\ge0$ generalizes the printed quantile. Both value sets are nonempty and bounded, so their real infima and suprema represent the stated minima and maxima.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 11, Proposition 1 and (26)–(28); proof p. 24

import Mathlib
import Definitions.Def_EmpiricalDRO_Discrete_Setting

namespace EmpiricalDRO.Discrete

/-- Proposition 1, p. 11: on finite support, the lower and upper empirical DRO values
equal the corresponding finite-support Burg-divergence DRO values. -/
theorem proposition1_discrete_reduction {n k : ℕ} (hn : 0 < n)
    {Ξ : Type*} (s : Fin k → Ξ) (c : Fin n → Fin k)
    {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → Ξ → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (κ : ℝ) (hκ : 0 ≤ κ) :
    EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (κ / 2) (fun j => h x (s (c j))) =
      sInf ((fun p : Fin k → ℝ => ∑ i, p i * h x (s i)) ''
        burgBall (phat c) (κ / (2 * n))) ∧
    GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (κ / 2) (fun j => h x (s (c j))) =
      sSup ((fun p : Fin k → ℝ => ∑ i, p i * h x (s i)) ''
        burgBall (phat c) (κ / (2 * n))) := by sorry

end EmpiricalDRO.Discrete
