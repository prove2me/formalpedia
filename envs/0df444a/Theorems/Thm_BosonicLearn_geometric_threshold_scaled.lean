-- Prove2me | Theorems.Thm_BosonicLearn_geometric_threshold_scaled
-- name    : BosonicLearn.geometric_threshold_scaled
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:08:46.097118+00:00
-- url     : https://prove2.me/theorems/0cb4fe6b-504c-4dfe-9bc0-c94571a10e3d
-- title:
--   Threshold separation for sums of geometric variables, uniform in the scale $\Lambda$ of the means (binomial thinning)
-- statement:
--   A version of `BosonicLearn.geometric_pgf_threshold` whose constant does not depend on the bound $\Lambda$ of the means; it is what makes the photon-counting argument of Lemma 12 work for hot states ($\nu\ge1$, Theorem 9).
--
--   There is an absolute constant $c>0$ such that for every $\Lambda\ge1$: let $0\le\lambda^-_i\le\lambda^+_i\le\Lambda$ ($i=1,\dots,m$) and let $p^\pm$ be the laws on $\mathbb N$ of $K_\pm=\sum_iM^\pm_i$, sums of independent geometric variables with means $\lambda^\pm_i$, given through $\sum_kp^\pm_kz^k=\prod_i\frac{1}{1+\lambda^\pm_i(1-z)}$ for $0\le z\le1$. Put $\delta=\sum_i(\lambda^+_i-\lambda^-_i)$. If $0<\delta$ and $\delta^2\le1+\sum_i\lambda^-_i(1+\lambda^-_i)$, then there is a threshold $\tau$ with
--
--   $$\Pr(K_+>\tau)-\Pr(K_->\tau)\ \ge\ c\,\frac{\delta/\Lambda}{\sqrt{1+\sum_i\frac{\lambda^-_i}{\Lambda}\big(1+\frac{\lambda^-_i}{\Lambda}\big)}} .$$
--
--   Proof idea: binomial thinning with probability $1/\Lambda$ maps a sum of geometric variables with means $\lambda_i$ to one with means $\lambda_i/\Lambda\le1$ (the generating function is evaluated at $1-\eta+\eta z$), and a thinned threshold test is a mixture of threshold tests (Abel summation), so the $\Lambda=1$ case applies.
--
--   **Formalization Note** Laws are sequences `ℕ → ℝ` with non-negative entries determined by the generating-function identities; tails are `∑' k, if τ < k then p k else 0`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.7, Lemmas 13–14 and Eqs. (137)–(142); used for §8, proof of Theorem 9, p. 66

import Mathlib

namespace BosonicLearn

/-- **Threshold separation for sums of geometric variables, uniformly in the scale of the means.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.7, Lemmas 13–14 and Eqs. (137)–(142) (threshold separation for the photon count), used in §8 for hot states
(`ν ≥ 1`, proof of Theorem 9, p. 66).

There is an absolute constant `c > 0` such that for every `Λ ≥ 1`: let `0 ≤ λ⁻_i ≤ λ⁺_i ≤ Λ` and let `p⁺, p⁻` be the laws
on `ℕ` of sums of independent geometric variables with means `λ^±_i` (given through their generating functions
`∑ₖ p^±_k zᵏ = ∏ᵢ 1/(1 + λ^±_i(1 − z))`, `0 ≤ z ≤ 1`). Put `δ = ∑ᵢ(λ⁺_i − λ⁻_i)`. If `0 < δ` and
`δ² ≤ 1 + ∑ᵢ λ⁻_i(1 + λ⁻_i)`, then there is a threshold `τ` with

`Pr(K₊ > τ) − Pr(K₋ > τ) ≥ c (δ/Λ) / √(1 + ∑ᵢ (λ⁻_i/Λ)(1 + λ⁻_i/Λ))`.

**Formalization Note.** This is `geometric_pgf_threshold` (whose constant depends on the bound `Λ` of the means) made
uniform: binomial thinning with probability `1/Λ` maps a sum of geometric variables with means `λ_i` to one with means
`λ_i/Λ ≤ 1`, and a thinned threshold test is a mixture of threshold tests. -/
theorem geometric_threshold_scaled :
    ∃ c : ℝ, 0 < c ∧ ∀ Λ : ℝ, 1 ≤ Λ →
      ∀ (m : ℕ) (lp lm : Fin m → ℝ), (∀ i, 0 ≤ lm i) → (∀ i, lm i ≤ lp i) → (∀ i, lp i ≤ Λ) →
      ∀ (pp pm : ℕ → ℝ), (∀ k, 0 ≤ pp k) → (∀ k, 0 ≤ pm k) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pp k * z ^ k) (∏ i, (1 + lp i * (1 - z))⁻¹)) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pm k * z ^ k) (∏ i, (1 + lm i * (1 - z))⁻¹)) →
        0 < ∑ i, (lp i - lm i) →
        (∑ i, (lp i - lm i)) ^ 2 ≤ 1 + ∑ i, lm i * (1 + lm i) →
        ∃ τ : ℕ, c * ((∑ i, (lp i - lm i)) / Λ) /
            Real.sqrt (1 + ∑ i, lm i / Λ * (1 + lm i / Λ)) ≤
          (∑' k, if τ < k then pp k else 0) - ∑' k, if τ < k then pm k else 0 := by sorry

end BosonicLearn
