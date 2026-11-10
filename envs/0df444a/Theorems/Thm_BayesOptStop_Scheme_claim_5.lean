-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_claim_5
-- name    : BayesOptStop.Scheme.claim_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:19:49.815494+00:00
-- url     : https://prove2.me/theorems/057b8b5f-6696-4b61-95c2-bf202feee35f
-- title:
--   Claim 5 — bounds on $1/G_{\ell-1}$
-- statement:
--   Suppose $0<\alpha_0\le1$ and $\alpha_{q+1}=1/(1+\ln(1/\alpha_q))$ for every $q\ge0$. For every $\ell\ge1$ and $j\ge1$ respectively,
--   $$\frac1{G_{\ell-1}}\le\frac{4^{\ell-1}}{\alpha_0^2}\qquad\text{and}\qquad\prod_{\ell=1}^j\frac1{G_{\ell-1}}\le\frac{4^{j(j-1)/2}}{\alpha_0^{2j}},$$
--   where $G_{\ell-1}=\prod_{q=0}^{\ell-1}\alpha_q$.
--
--   Differences from the source:
--   - encoding: G_{ℓ-1} = ∏_{q=0}^{ℓ-1} α_q → Gprod α₀ ℓ = ∏_{q<ℓ} α_q; reason: index shift; avoids natural subtraction
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Claim 5, p. 43 (proof App. B.4.1, p. 44)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement

namespace BayesOptStop.Scheme

/-- **Claim 5** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 43): if `0 < α₀ ≤ 1` and `α_{q+1} = 1/(1 + ln(1/α_q))`, then for every
`ℓ ≥ 1`, `1/G_{ℓ-1} ≤ 4^{ℓ-1}/α₀²`, and for every `j ≥ 1`,
`∏_{ℓ=1}^j 1/G_{ℓ-1} ≤ 4^{j(j-1)/2}/α₀^{2j}`, where `G_{ℓ-1} = ∏_{q<ℓ} α_q`. -/
theorem claim_5 (α₀ : ℝ) (hα0 : 0 < α₀) (hα1 : α₀ ≤ 1) :
    (∀ ℓ : ℕ, 1 ≤ ℓ → 1 / Gprod α₀ ℓ ≤ (4 : ℝ) ^ (ℓ - 1) / α₀ ^ 2) ∧
      ∀ j : ℕ, 1 ≤ j →
        ∏ ℓ ∈ Finset.Icc 1 j, 1 / Gprod α₀ ℓ ≤ (4 : ℝ) ^ (j * (j - 1) / 2) / α₀ ^ (2 * j) := by sorry

end BayesOptStop.Scheme
