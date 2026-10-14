-- Prove2me | Theorems.Thm_BudgetedAffine_Budget_claim_3_3
-- name    : BudgetedAffine.Budget.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:36.241298+00:00
-- url     : https://prove2.me/theorems/df20e784-f2a0-459c-a47f-70592afe2e45
-- title:
--   Claim 3.3 — P(Σ_{i∈J} w_i Z_i > 1/2) ≥ 1 − e^{−1/8}
-- statement:
--   Let $\mathcal J\subseteq[m]$, $w_i\in(0,1]$ and $z^*_i\ge0$ for $i\in\mathcal J$, with
--   $$\sum_{i\in\mathcal J}w_iz^*_i>1.$$
--   Let $\xi_i\sim\mathrm{Ber}(z^*_i-\lfloor z^*_i\rfloor)$ be independent and $Z_i=\lfloor z^*_i\rfloor+\xi_i$. Then
--   $$\mathbb P\Big(\sum_{i\in\mathcal J}w_iZ_i>\tfrac12\Big)\ge1-e^{-1/8}.$$
--
--   Together with Claim 3.2 this shows that the rounded dual solution is, with positive probability, both feasible and of value larger than $1/\eta$.
--
--   **Formalization Note** In the paper $z^*$ is the optimal solution of (3.7) and $\sum_{i\in\mathcal J}w_iz^*_i=\hat z(\mathcal J)>1$ by LP duality under the contradiction hypothesis of Section 3.3. The statement assumes only the two facts its proof uses ($z^*\ge0$ on $\mathcal J$ and $\sum_{i\in\mathcal J}w_iz^*_i>1$), so it applies to the paper's $z^*$. Probabilities are those of independent Bernoulli selection from $\mathcal J$ (the referenced definition `SpectralSparsify.Sampling.BernoulliSubset`): the outcome is the set $T\subseteq\mathcal J$ of indices with $\xi_i=1$, and $Z_i=\lfloor z^*_i\rfloor+\mathbb 1[i\in T]$.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Claim 3.3, p. 13 (proof App. A, p. 32)

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset

namespace BudgetedAffine.Budget

open SpectralSparsify.Sampling

/-- Claim 3.3: if `z*ᵢ ≥ 0` and `wᵢ ∈ (0,1]` for `i ∈ J` with `∑_{i ∈ J} wᵢ z*ᵢ > 1`, and
`Zᵢ = ⌊z*ᵢ⌋ + ξᵢ` with independent `ξᵢ ~ Ber(z*ᵢ − ⌊z*ᵢ⌋)` for `i ∈ J` (the outcome is the set
`T ⊆ J` of indices with `ξᵢ = 1`), then `P(∑_{i ∈ J} wᵢ Zᵢ > 1/2) ≥ 1 − e^{−1/8}`. -/
theorem claim_3_3 {m : ℕ} (J : Finset (Fin m)) (w zs : Fin m → ℝ)
    (hw : ∀ i ∈ J, 0 < w i ∧ w i ≤ 1) (hz : ∀ i ∈ J, 0 ≤ zs i)
    (hsum : 1 < ∑ i ∈ J, w i * zs i) :
    1 - Real.exp (-(1 / 8)) ≤
      prob J (fun i => zs i - ⌊zs i⌋)
        (fun T => 1 / 2 < ∑ i ∈ J, w i * ((⌊zs i⌋ : ℝ) + if i ∈ T then 1 else 0)) := by sorry

end BudgetedAffine.Budget
