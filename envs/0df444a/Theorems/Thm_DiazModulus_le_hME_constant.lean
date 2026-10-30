-- Prove2me | Theorems.Thm_DiazModulus_le_hME_constant
-- name    : DiazModulus.le_hME_constant
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:45.087359+00:00
-- url     : https://prove2.me/theorems/4bf0048f-e5f2-49db-be46-bd3dc458f192
-- title:
--   $\lambda\, 2^{r(r-1)/2} \le 2^{rd} D_0^{d_0} (2D_1)^{d_1}$ implies $\lambda \le 2^{d(d+1)/2}\, d!\, 2^{d_1} d_0^{d_0} D_0^{d_0} D_1^{d_1}$, the constant of the elementary multiplicity estimate
-- statement:
--   Let $\lambda, r, d_0, d_1, D_0, D_1 \in \mathbb{N}$ and $d = d_0 + d_1$. If $\lambda\, 2^{r(r-1)/2} \le 2^{rd} D_0^{d_0} (2D_1)^{d_1}$, then $\lambda \le 2^{d(d+1)/2}\, d!\, 2^{d_1} d_0^{d_0} \cdot D_0^{d_0} D_1^{d_1}$, with $0^0 = 1$ (the exponents $r(r-1)/2$ and $d(d+1)/2$ are integers). For $d_0 = |A_0|$ and $d_1 = |A_1|$ the factor $2^{d(d+1)/2}\, d!\, 2^{d_1} d_0^{d_0}$ is the constant $K_d$ of the Definition `MultiplicityEstimateElem`, the elementary multiplicity estimate.
--
--   **Proof.** For every $r$, $rd \le d(d+1)/2 + r(r-1)/2$, since $d(d+1) + r(r-1) - 2rd = (d - r)(d - r + 1) \ge 0$. So $2^{rd} \le 2^{d(d+1)/2} 2^{r(r-1)/2}$, and cancelling $2^{r(r-1)/2}$ gives $\lambda \le 2^{d(d+1)/2} 2^{d_1} D_0^{d_0} D_1^{d_1}$; the factors $d!$ and $d_0^{d_0}$ are at least $1$.
--
--   **Novelty.** Not found in the sources read in this form; routine. Elementary arithmetic; no condition on $r$ is needed.
-- source:
--   Elementary. The constant is that of the elementary multiplicity estimate, the case G⁻ = {e} of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.1 (§8.1, p. 232; Chapter 8 is by D. Roy), in coordinates. Not found in the sources read in this form; routine. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem le_hME_constant (lam r d₀ d₁ D₀ D₁ : ℕ)
    (h : lam * 2 ^ (r * (r - 1) / 2) ≤ 2 ^ (r * (d₀ + d₁)) * (D₀ ^ d₀ * (2 * D₁) ^ d₁)) :
    lam ≤ (2 ^ ((d₀ + d₁) * (d₀ + d₁ + 1) / 2) * (d₀ + d₁).factorial * 2 ^ d₁ * d₀ ^ d₀)
      * D₀ ^ d₀ * D₁ ^ d₁ := by
  sorry

end DiazModulus
