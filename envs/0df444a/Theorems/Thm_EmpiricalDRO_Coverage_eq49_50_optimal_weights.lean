-- Prove2me | Theorems.Thm_EmpiricalDRO_Coverage_eq49_50_optimal_weights
-- name    : EmpiricalDRO.Coverage.eq49_50_optimal_weights
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:24.003531+00:00
-- url     : https://prove2.me/theorems/fed2566c-145a-443f-9b6f-249a2640b566
-- title:
--   (47), (49)–(50), pp. 25–26 — if min zᵢ < μ < max zᵢ, wᵢ = (1/n)/(1 + λ(zᵢ − μ)) is the unique optimum defining −2 log R(μ)
-- statement:
--   Let $n\ge1$, let $z_1,\dots,z_n$ be real numbers (the values $h(x;\xi_i)$ at a fixed decision $x$) and let $\mu\in\mathbb R$ (the mean $Z_0(x)$) satisfy
--   $$
--   \min_{1\le i\le n}z_i<\mu<\max_{1\le i\le n}z_i .
--   $$
--   Write $\tilde h_i=z_i-\mu$. Then there is a real number $\lambda$ such that
--
--   1. $1+\lambda\tilde h_i>0$ for every $i$;
--   2. $\lambda$ solves equation (50):
--   $$
--   \sum_{i=1}^n\frac1n\,\frac{\tilde h_i}{1+\lambda\tilde h_i}=0;
--   $$
--   3. the weights of (49),
--   $$
--   w_i=\frac1n\,\frac1{1+\lambda\tilde h_i},\qquad i=1,\dots,n,
--   $$
--   are strictly positive, sum to $1$ and satisfy $\sum_i w_iz_i=\mu$, i.e. they are feasible for the optimization (47);
--   4. $w$ is the unique minimizer of $-\sum_i\log(nw_i)$ over all strictly positive weight vectors $w'\ne w$ with $\sum_i w'_i=1$ and $\sum_i w'_iz_i=\mu$: for each such $w'$, $-\sum_i\log(nw_i)<-\sum_i\log(nw'_i)$;
--   5. consequently $-2\log R(\mu)=-2\sum_i\log(nw_i)$.
--
--   This identifies the optimal weights of the profile likelihood (47) in closed form through a single scalar multiplier, which is the starting point of the asymptotic expansion of $-2\log R$.
--
--   **Formalization Note.** This is the step of the proof of Theorem 5 specialised to a single decision point $x$ ($\Theta=\{x\}$); the vector $z$ stands for the sample values and $\mu$ for $Z_0(x)$. The multiplier is the paper's rescaled $\lambda$ (written `lam` in Lean). Weight vectors with a zero coordinate are excluded from the comparison, as the paper excludes them ("setting any $w_i(x)=0$ would render $-2\sum\log(nw_i)=\infty$"). $-2\log R(\mu)$ is the mission's statistic `elStat`.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, pp. 25–26, proof of Theorem 5, (47), (49), (50)

import Mathlib
import Definitions.Def_EmpiricalDRO_Coverage_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Coverage

/-- (47), (49)–(50), Lam, arXiv:1605.09349v1, pp. 25–26, for one decision point: if
`min zᵢ < μ < max zᵢ`, there is a (rescaled) multiplier `lam` with `1 + lam (zᵢ − μ) > 0` solving (50),
and the weights `wᵢ = (1/n) · 1/(1 + lam (zᵢ − μ))` of (49) are feasible for (47), are its unique
minimiser among strictly positive feasible weights, and attain `−2 log R(μ) = elStat z μ`. -/
theorem eq49_50_optimal_weights {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ : ℝ)
    (hlo : ∃ i, z i < μ) (hhi : ∃ i, μ < z i) :
    ∃ lam : ℝ, (∀ i, 0 < 1 + lam * (z i - μ)) ∧
      ∑ i, (1 / (n : ℝ)) * ((z i - μ) / (1 + lam * (z i - μ))) = 0 ∧
      let w : Fin n → ℝ := fun i => 1 / ((n : ℝ) * (1 + lam * (z i - μ)))
      ((∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i * z i = μ) ∧
      (∀ w' : Fin n → ℝ, (∀ i, 0 < w' i) → ∑ i, w' i = 1 → ∑ i, w' i * z i = μ → w' ≠ w →
        -∑ i, Real.log (n * w i) < -∑ i, Real.log (n * w' i)) ∧
      elStat z μ = ((-2 * ∑ i, Real.log (n * w i) : ℝ) : EReal) := by sorry

end EmpiricalDRO.Coverage
