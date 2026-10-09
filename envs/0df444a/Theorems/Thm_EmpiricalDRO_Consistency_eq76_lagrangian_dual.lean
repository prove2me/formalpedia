-- Prove2me | Theorems.Thm_EmpiricalDRO_Consistency_eq76_lagrangian_dual
-- name    : EmpiricalDRO.Consistency.eq76_lagrangian_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:29.980004+00:00
-- url     : https://prove2.me/theorems/f8ec1475-72ac-48d0-bb34-8eb52e5c609f
-- title:
--   (75)–(76), p. 33 — Z̄_n(x) − Z0(x) equals min_{λ≥0,γ} −Σ (λ/n) log(1 − (h̃_i + γ)/λ) + λ q/(2n) − γ
-- statement:
--   Let $n\ge1$, let $z=(z_1,\dots,z_n)$ be real numbers, let $\mu\in\mathbb R$ and $q>0$, and write $\tilde h_i=z_i-\mu$. Let $\overline Z_n=\max\{\sum_i z_iw_i: w\in\mathcal U_n(q/(2n))\}$ be the maximum over the empirical Burg ball (19) of radius $q/(2n)$. Then
--   $$
--   \overline Z_n-\mu=\min_{\lambda\ge0,\ \gamma\in\mathbb R}\ -\sum_{i=1}^n\frac{\lambda}{n}\log\Big(1-\frac{\tilde h_i+\gamma}{\lambda}\Big)+\lambda\frac{q}{2n}-\gamma,
--   $$
--   where $-\lambda\log(1-t/\lambda)$ is read as $+\infty$ when $\lambda>0$ and $t\ge\lambda$, and, at $\lambda=0$, $-0\log(1-t/0):=0$ for $t\le0$ and $:=\infty$ for $t>0$.
--
--   This is the Lagrangian dual of the program (75) in the proof of Theorem 6, specialized to one decision $x$, with $z_i=h(x;\xi_i)$, $\mu=Z_0(x)$ and $q=\chi^2_{1,1-\alpha}$. It turns the maximization over weights into a two-parameter minimization, any feasible point of which bounds $\overline Z_n-\mu$ from above.
--
--   **Formalization Note** The identity is stated in `EReal`; the dual summand is `dualTerm`, the infimum ranges over $\lambda\ge0$ and all real $\gamma$, and the radius is $q/(2n)$, i.e. $\rho=q/2$ in `robustMean`'s radius $\rho/n$. The hypothesis $q>0$ is the Slater condition: the uniform weight has divergence $0<q/(2n)$. The page prints the left side as $\overline Z_n(x)$ with radius $q_n/(2n)$; for a single decision $q_n=\chi^2_{1,1-\alpha}$, and the statement holds for every $q>0$.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 33, proof of Theorem 6, (75)–(76); convention for λ = 0 and the conjugate of −log r + r − 1 on p. 34

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Consistency

/-- (75)–(76), Lam, arXiv:1605.09349v1, p. 33, at a single decision (radius `q/(2n)`): for a sample
`z` of size `n ≥ 1`, a centring constant `μ` and `q > 0`, the upper robust value minus `μ`
equals the Lagrangian dual
`min_{λ ≥ 0, γ} ∑ᵢ (1/n) (−λ log(1 − (zᵢ − μ + γ)/λ)) + λ q/(2n) − γ`,
with the convention of `dualTerm` at `λ = 0` and for `zᵢ − μ + γ ≥ λ`. -/
theorem eq76_lagrangian_dual {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ q : ℝ) (hq : 0 < q) :
    ((GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) z - μ : ℝ) : EReal) =
      ⨅ (lam : ℝ) (_ : 0 ≤ lam) (γ : ℝ),
        (∑ i, ((1 / (n : ℝ) : ℝ) : EReal) * dualTerm lam (z i - μ + γ)) +
          ((lam * (q / (2 * n)) - γ : ℝ) : EReal) := by sorry

end EmpiricalDRO.Consistency
