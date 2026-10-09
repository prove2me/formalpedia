-- Prove2me | Theorems.Thm_EmpiricalDRO_Coverage_eq52_multiplier_bound
-- name    : EmpiricalDRO.Coverage.eq52_multiplier_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:29.965624+00:00
-- url     : https://prove2.me/theorems/49fa4fb2-6df4-4b8a-a4fc-9b6f0c8a32df
-- title:
--   (52), p. 27 — |λ| (s − |h̄| max_i |h̃_i|) ≤ |h̄|
-- statement:
--   Let $n\ge1$, $z_1,\dots,z_n,\mu\in\mathbb R$, and write $\tilde h_i=z_i-\mu$,
--   $$
--   \bar h=\frac1n\sum_{i=1}^n\tilde h_i,\qquad s=\frac1n\sum_{i=1}^n\tilde h_i^2 .
--   $$
--   Let $\lambda\in\mathbb R$ satisfy $1+\lambda\tilde h_i>0$ for every $i$ and equation (50), $\sum_i\frac1n\frac{\tilde h_i}{1+\lambda\tilde h_i}=0$. Then
--   $$
--   |\lambda|\Big(s-|\bar h|\max_{1\le i\le n}|\tilde h_i|\Big)\le|\bar h| .
--   $$
--
--   Together with $\bar h=O_p(n^{-1/2})$, $s\to\operatorname{Var}$ and $\max_i|\tilde h_i|=o(n^{1/2})$, this inequality shows that the multiplier of the optimal weights is $O_p(n^{-1/2})$.
--
--   **Formalization Note.** Specialised to a single decision point $x$ ($\Theta=\{x\}$): $z$ stands for the sample values $h(x;\xi_i)$, $\mu$ for $Z_0(x)$, and the norms $\|\cdot\|_\Theta$ of the paper become absolute values. The statement is deterministic: it holds for every data vector. Note that $s$ is centred at $\mu$, not at the sample mean.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 27, proof of Theorem 5, (52) (from (50)–(51))

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Coverage

/-- (52), Lam, arXiv:1605.09349v1, p. 27, for one decision point: with `h̃ᵢ = zᵢ − μ`,
`h̄ = (1/n) ∑ h̃ᵢ`, `s = (1/n) ∑ h̃ᵢ²`, if `1 + lam h̃ᵢ > 0` for all `i` and `lam` solves (50), then
`|lam| (s − |h̄| max |h̃ᵢ|) ≤ |h̄|`. -/
theorem eq52_multiplier_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ lam : ℝ)
    (hpos : ∀ i, 0 < 1 + lam * (z i - μ))
    (h50 : ∑ i, (1 / (n : ℝ)) * ((z i - μ) / (1 + lam * (z i - μ))) = 0) :
    |lam| * ((1 / (n : ℝ)) * ∑ i, (z i - μ) ^ 2 -
        |(1 / (n : ℝ)) * ∑ i, (z i - μ)| * ⨆ i, |z i - μ|) ≤
      |(1 / (n : ℝ)) * ∑ i, (z i - μ)| := by sorry

end EmpiricalDRO.Coverage
