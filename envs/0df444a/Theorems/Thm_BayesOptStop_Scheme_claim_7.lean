-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_claim_7
-- name    : BayesOptStop.Scheme.claim_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:19:35.629204+00:00
-- url     : https://prove2.me/theorems/1466dc44-c597-46b9-b307-99af040a9874
-- title:
--   Claim 7 — the propagated failure probabilities $p_\ell=\ln(4n/\kappa_\ell)$
-- statement:
--   For $0\le\ell\le j$ let $p_\ell=\ln(4n/\kappa_\ell)$ and $L=\ln(96\cdot9^jn^2/(\alpha_0^2\kappa\eta^2))$, where $\kappa_j=\kappa$, $\kappa_{\ell-1}=\kappa_\ell/(2B_\ell)$, $B_\ell=nI_\ell+1$, $I_\ell=\lceil3/(\eta_{\ell-1}^2G_{\ell-1})\ln(4n/\kappa_\ell)\rceil$ are the parameters of a level-$j$ call of Algorithm 3 with accuracy parameters $(\eta,\kappa)$. Then
--   $$p_\ell\le2^{j-\ell}L\qquad\text{and}\qquad\prod_{\ell=1}^jp_\ell\le2^{j(j-1)/2}L^j.$$
--
--   Differences from the source:
--   - reading: Claim 7 states no ranges → 0 < α₀ ≤ 1, 0 < η < 1, 0 < κ < 1, n ≥ 1; reason: these are the hypotheses of Claim 3, whose runtime analysis (App. B.4) defines κ_ℓ, η_ℓ and G_{ℓ−1}
--   - encoding: κ_ℓ defined by downward recursion from κ_j = κ → kappaLevel α₀ η κ n j ℓ = kappaDown … (j − ℓ), with I_ℓ a natural-number ceiling; reason: index convention
--   - generalization: the runtime analysis fixes a positive recursion level j → j = 0 is also admitted; reason: the product bound is 1 ≤ 1, and the sole pointwise bound is ln(4n/κ) ≤ ln(96n²/(α₀²κη²)) under the same parameter ranges
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Claim 7, p. 43 (proof App. B.4.3, p. 44)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement

namespace BayesOptStop.Scheme

/-- **Claim 7** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 43): for `0 ≤ ℓ ≤ j` let `p_ℓ = ln(4n/κ_ℓ)` (the propagated failure
probabilities `κ_ℓ` of a level-`j` call of Algorithm 3 with parameters `(η, κ)`, App. B.4) and
`L = ln(96 · 9^j n²/(α₀² κ η²))`. Then `p_ℓ ≤ 2^{j-ℓ} L` and `∏_{ℓ=1}^j p_ℓ ≤ 2^{j(j-1)/2} L^j`. -/
theorem claim_7 (α₀ η κ : ℝ) (n j : ℕ) (hα0 : 0 < α₀) (hα1 : α₀ ≤ 1) (hη0 : 0 < η)
    (hη1 : η < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hn : 1 ≤ n) :
    (∀ ℓ : ℕ, ℓ ≤ j → pLevel α₀ η κ n j ℓ ≤
        (2 : ℝ) ^ (j - ℓ) * Real.log (96 * 9 ^ j * (n : ℝ) ^ 2 / (α₀ ^ 2 * κ * η ^ 2))) ∧
      ∏ ℓ ∈ Finset.Icc 1 j, pLevel α₀ η κ n j ℓ ≤
        (2 : ℝ) ^ (j * (j - 1) / 2) *
          Real.log (96 * 9 ^ j * (n : ℝ) ^ 2 / (α₀ ^ 2 * κ * η ^ 2)) ^ j := by sorry

end BayesOptStop.Scheme
