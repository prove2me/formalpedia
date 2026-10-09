-- Prove2me | Theorems.Thm_EmpiricalDRO_Consistency_eq77_upper_bound
-- name    : EmpiricalDRO.Consistency.eq77_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:07:28.275233+00:00
-- url     : https://prove2.me/theorems/7ed7996a-4e87-497a-9842-535b3c0c6c2e
-- title:
--   (77), p. 34 — Z̄_n(x) − Z0(x) ≤ (1/n)Σ h̃_i + 2((1/n)Σ h̃_i²)/λ + λ q/(2n) when max_i |h̃_i| ≤ λ/2
-- statement:
--   Let $n\ge1$, let $z=(z_1,\dots,z_n)$ be real numbers, let $\mu\in\mathbb R$, $q\ge0$ and $\lambda>0$, and write $\tilde h_i=z_i-\mu$. Let $\overline Z_n$ be the maximum of $\sum_i z_iw_i$ over the empirical Burg ball $\mathcal U_n(q/(2n))$ of (19). If
--   $$
--   \max_{1\le i\le n}|\tilde h_i|\le\frac{\lambda}{2},
--   $$
--   then
--   $$
--   \overline Z_n-\mu\ \le\ \frac1n\sum_{i=1}^n\tilde h_i+2\,\frac{(1/n)\sum_{i=1}^n\tilde h_i^{2}}{\lambda}+\lambda\frac{q}{2n}.
--   $$
--
--   This is the bound (77) in the proof of Theorem 6, specialized to one decision $x$ ($z_i=h(x;\xi_i)$, $\mu=Z_0(x)$, $q=\chi^2_{1,1-\alpha}$): the dual (76) evaluated at $\gamma=0$ and $\lambda=\lambda_n$. With $\lambda_n$ of order $n^{\varepsilon}$, $1/2<\varepsilon<1$, all three terms tend to $0$ almost surely, which gives the upper half of the consistency of $\overline Z_n(x)$.
--
--   **Formalization Note** The bound is deterministic and holds for every $\lambda>0$ satisfying the hypothesis; the asymptotic choice $\lambda_n=\Theta(n^\varepsilon)$ and the event "eventually" belong to the proof of Theorem 3. The radius $q/(2n)$ is $\rho=q/2$ in `robustMean`'s radius $\rho/n$.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 34, proof of Theorem 6, (77) and the two sentences before it

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Consistency

/-- (77), Lam, arXiv:1605.09349v1, p. 34, at a single decision: if every centred observation
satisfies `|zᵢ − μ| ≤ λ/2` for some `λ > 0`, then
`Z̄_n − μ ≤ (1/n) ∑ᵢ (zᵢ − μ) + 2 ((1/n) ∑ᵢ (zᵢ − μ)²)/λ + λ q/(2n)`,
where `Z̄_n` is the upper robust value over the Burg ball of radius `q/(2n)`. -/
theorem eq77_upper_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ q lam : ℝ) (hq : 0 ≤ q)
    (hlam : 0 < lam) (hmax : ∀ i, |z i - μ| ≤ lam / 2) :
    GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) z - μ ≤
      (1 / (n : ℝ)) * ∑ i, (z i - μ) + 2 * ((1 / (n : ℝ)) * ∑ i, (z i - μ) ^ 2) / lam +
        lam * (q / (2 * n)) := by sorry

end EmpiricalDRO.Consistency
