-- Prove2me | Theorems.Thm_BosonicLearn_geometric_pgf_threshold
-- name    : BosonicLearn.geometric_pgf_threshold
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:00:07.260824+00:00
-- url     : https://prove2.me/theorems/ea5973e1-0a8e-405a-a174-02b8d78c5163
-- title:
--   Threshold separation for sums of independent geometric variables: $\Pr(K_+>\tau)-\Pr(K_->\tau)\ge c\,\delta/s$ (Lemmas 13–14)
-- statement:
--   Lemmas 13 and 14 of the paper, combined and specialized to the photon-count distributions of the proof of Lemma 12.
--
--   Fix $\Lambda>0$. There is a constant $c=c(\Lambda)>0$ with the following property. Let $0\le\lambda^-_i\le\lambda^+_i\le\Lambda$ for $i=1,\dots,m$, and let
--
--   $$
--   K_+=\sum_{i=1}^mM^+_i,\qquad K_-=\sum_{i=1}^mM^-_i
--   $$
--
--   be sums of independent geometric random variables on $\{0,1,2,\dots\}$ with means $\lambda^\pm_i$ (so $\mathbb E\,z^{K_\pm}=\prod_i\frac1{1+\lambda^\pm_i(1-z)}$). Put
--
--   $$
--   \delta=\sum_i(\lambda^+_i-\lambda^-_i),\qquad s^2=1+\operatorname{Var}(K_-)=1+\sum_i\lambda^-_i(1+\lambda^-_i).
--   $$
--
--   If $0<\delta\le s$, then there is a threshold $\tau\in\mathbb N$ such that
--
--   $$
--   \Pr(K_+>\tau)-\Pr(K_->\tau)\ \ge\ c\,\frac\delta s .
--   $$
--
--   Role. In the proof of Lemma 12, $K_\pm$ are the photon counts in a subspace of modes for the two passive Gaussian states; the linear dependence on $\delta/s$ (rather than the quadratic one a second-moment argument would give) is what yields the trace-distance bound $\gtrsim\xi\sqrt{n\nu}$.
--
--   **Formalization Note** The two laws are sequences `pp pm : ℕ → ℝ` with non-negative entries, specified through their probability generating functions on $[0,1]$ (`HasSum (fun k => p k * z ^ k) (∏ i, (1 + λ i * (1 - z))⁻¹)`), which determine them; at $z=1$ this says they have total mass one. The hypothesis $\delta\le s$ is written $\delta^2\le s^2$. The constant depends only on $\Lambda$ (the proof gives $c=1/(480+70\Lambda)$).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.7, Lemma 13 (coarse Lévy concentration bound), Lemma 14 (threshold separation under convolution order), and Eqs. (137)–(142)

import Mathlib

namespace BosonicLearn

/-- **Threshold separation for sums of independent geometric variables (Lemmas 13 and 14 combined).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.7, Lemma 13 (coarse Lévy concentration bound), Lemma 14 (threshold separation under convolution order), and the coupling
of Eqs. (137)–(142).

Fix `Λ > 0`. There is `c > 0` such that the following holds. Let `0 ≤ λ⁻_i ≤ λ⁺_i ≤ Λ` (`i = 1, …, m`), and let
`p⁺, p⁻` be the laws on `ℕ` of `K₊ = ∑ᵢ M⁺ᵢ` and `K₋ = ∑ᵢ M⁻ᵢ`, sums of independent geometric variables with
means `λ^±_i` — given through their probability generating functions
`∑ₖ p^±_k zᵏ = ∏ᵢ 1/(1 + λ^±_i (1 − z))`, `0 ≤ z ≤ 1`. Put `δ = ∑ᵢ (λ⁺_i − λ⁻_i)` and
`s² = 1 + Var(K₋) = 1 + ∑ᵢ λ⁻_i(1 + λ⁻_i)`. If `0 < δ ≤ s`, then there is a threshold `τ` with

`Pr(K₊ > τ) − Pr(K₋ > τ) ≥ c δ / s`.

**Formalization Note.** The laws are sequences `ℕ → ℝ` with non-negative entries, determined by the generating
function identities (at `z = 1` they give total mass one). `δ ≤ s` is written `δ² ≤ s²`. -/
theorem geometric_pgf_threshold :
    ∀ Λ : ℝ, 0 < Λ → ∃ c : ℝ, 0 < c ∧
      ∀ (m : ℕ) (lp lm : Fin m → ℝ), (∀ i, 0 ≤ lm i) → (∀ i, lm i ≤ lp i) → (∀ i, lp i ≤ Λ) →
      ∀ (pp pm : ℕ → ℝ), (∀ k, 0 ≤ pp k) → (∀ k, 0 ≤ pm k) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pp k * z ^ k) (∏ i, (1 + lp i * (1 - z))⁻¹)) →
        (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          HasSum (fun k => pm k * z ^ k) (∏ i, (1 + lm i * (1 - z))⁻¹)) →
        0 < ∑ i, (lp i - lm i) →
        (∑ i, (lp i - lm i)) ^ 2 ≤ 1 + ∑ i, lm i * (1 + lm i) →
        ∃ τ : ℕ, c * (∑ i, (lp i - lm i)) / Real.sqrt (1 + ∑ i, lm i * (1 + lm i)) ≤
          (∑' k, if τ < k then pp k else 0) - ∑' k, if τ < k then pm k else 0 := by sorry

end BosonicLearn
