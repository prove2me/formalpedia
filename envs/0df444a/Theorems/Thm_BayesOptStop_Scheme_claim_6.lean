-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_claim_6
-- name    : BayesOptStop.Scheme.claim_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:19:59.941642+00:00
-- url     : https://prove2.me/theorems/6000f90b-736a-4ae7-8c2b-ec18372a6eb8
-- title:
--   Claim 6 — the propagated accuracies $\eta_{\ell-1}$
-- statement:
--   Let $\eta_j=\eta$ and $\eta_{\ell-1}=1-(1-\eta_\ell)^{1/3}$ (the accuracies of the recursive calls of Algorithm 3). For every $\ell\in[j]$, $\eta_{\ell-1}\ge\eta/3^{j-\ell+1}$, and consequently $\prod_{\ell=1}^j\eta_{\ell-1}^{-2}\le9^{j(j+1)/2}\eta^{-2j}$.
--
--   Differences from the source:
--   - reading: Claim 6 states no range for η → 0 < η < 1; reason: η is the accuracy parameter of Claim 3 (0 < η, κ < 1), whose runtime analysis Claim 6 serves
--   - encoding: η_{ℓ-1} defined by downward recursion from η_j = η → etaDown η (j − ℓ + 1); reason: index convention: etaDown η k = η_{j−k}
--   - generalization: the runtime analysis fixes a positive recursion level j → j = 0 is also admitted; reason: the pointwise clause is empty and the product bound is 1 ≤ 1
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Claim 6, p. 43 (proof App. B.4.2, p. 44)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement

namespace BayesOptStop.Scheme

/-- **Claim 6** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 43): with `η_j = η` and `η_{ℓ-1} = 1 - (1 - η_ℓ)^{1/3}`, for every
`ℓ ∈ [j]`, `η_{ℓ-1} ≥ η/3^{j-ℓ+1}`, and consequently `∏_{ℓ=1}^j η_{ℓ-1}^{-2} ≤ 9^{j(j+1)/2} η^{-2j}`.
Here `η_{ℓ-1} = etaDown η (j - ℓ + 1)`. -/
theorem claim_6 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (j : ℕ) :
    (∀ ℓ ∈ Finset.Icc 1 j, η / (3 : ℝ) ^ (j - ℓ + 1) ≤ etaDown η (j - ℓ + 1)) ∧
      ∏ ℓ ∈ Finset.Icc 1 j, 1 / etaDown η (j - ℓ + 1) ^ 2 ≤
        (9 : ℝ) ^ (j * (j + 1) / 2) / η ^ (2 * j) := by sorry

end BayesOptStop.Scheme
