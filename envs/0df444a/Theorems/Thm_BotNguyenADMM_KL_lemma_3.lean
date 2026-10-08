-- Prove2me | Theorems.Thm_BotNguyenADMM_KL_lemma_3
-- name    : BotNguyenADMM.KL.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:05.747623+00:00
-- url     : https://prove2.me/theorems/9bf29ca5-cbab-4891-97fc-470c38b441ef
-- title:
--   Lemma 3 — a three-step linear recursion with block-bounded perturbations has summable terms
-- statement:
--   Let $a^k=(a_1^k,\dots,a_N^k)\in\mathbb R^N_+$ and $\delta_k\in\mathbb R$ satisfy, for every $k\ge2$,
--   $$\langle\mathbb 1,a^{k+1}\rangle\le\langle c_0,a^k\rangle+\langle c_1,a^{k-1}\rangle+\langle c_2,a^{k-2}\rangle+\delta_k,$$
--   where $c_0\in\mathbb R^N$, $c_1,c_2\in\mathbb R^N_+$ and $c_0+c_1+c_2<\mathbb 1$ componentwise. Assume there is $\bar\delta\ge0$ with $\sum_{k=\underline K}^{\overline K}\delta_k\le\bar\delta$ for all $\overline K\ge\underline K\ge2$. Then $\sum_{k\ge0}a_i^k<+\infty$ for every $i$, and for every $i$ and every $\overline K\ge\underline K\ge2$,
--   $$\sum_{k=\underline K}^{\overline K}a_i^k\le\frac{\sum_{j=1}^N\big[(1-c_{0,j}-c_{1,j})a_j^{\underline K}+(1-c_{0,j})a_j^{\underline K+1}+a_j^{\underline K+2}\big]+\bar\delta}{1-c_{0,i}-c_{1,i}-c_{2,i}} .$$
--
--   It closes the proof of Theorem 14, applied with $N=1$ and $a^k=\|x^k-x^{k-1}\|$.
-- source:
--   Boţ and Nguyen, The proximal ADMM in the nonconvex setting, arXiv:1801.01994v2, p. 6, Lemma 3, (9)–(10)

import Mathlib
open Filter Topology

namespace BotNguyenADMM.KL

/-- Lemma 3 (p. 6). Let `aᵏ ∈ ℝᴺ₊` and `δ_k ∈ ℝ` satisfy
`⟨𝟙, aᵏ⁺¹⟩ ≤ ⟨c₀, aᵏ⟩ + ⟨c₁, aᵏ⁻¹⟩ + ⟨c₂, aᵏ⁻²⟩ + δ_k` for all `k ≥ 2` (9), where `c₀ ∈ ℝᴺ`,
`c₁, c₂ ∈ ℝᴺ₊` and `c₀ + c₁ + c₂ < 𝟙` componentwise, and let `δ̄ ≥ 0` bound every block sum
`∑_{k=K̲}^{K̄} δ_k` with `K̄ ≥ K̲ ≥ 2`. Then every coordinate sequence `(a_iᵏ)_k` is summable and
(10) holds for every `i` and every `K̄ ≥ K̲ ≥ 2`. -/
theorem lemma_3 (N : ℕ) (a : ℕ → Fin N → ℝ) (ha : ∀ k i, 0 ≤ a k i) (δ : ℕ → ℝ)
    (c₀ c₁ c₂ : Fin N → ℝ) (hc₁ : ∀ i, 0 ≤ c₁ i) (hc₂ : ∀ i, 0 ≤ c₂ i)
    (hc : ∀ i, c₀ i + c₁ i + c₂ i < 1)
    (h9 : ∀ k, 2 ≤ k → ∑ i, a (k + 1) i ≤
      ∑ i, c₀ i * a k i + ∑ i, c₁ i * a (k - 1) i + ∑ i, c₂ i * a (k - 2) i + δ k)
    (δbar : ℝ) (hδbar : 0 ≤ δbar)
    (hδ : ∀ Klo Khi : ℕ, 2 ≤ Klo → Klo ≤ Khi → ∑ k ∈ Finset.Icc Klo Khi, δ k ≤ δbar) :
    (∀ i, Summable (fun k => a k i)) ∧
    ∀ (i : Fin N) (Klo Khi : ℕ), 2 ≤ Klo → Klo ≤ Khi →
      ∑ k ∈ Finset.Icc Klo Khi, a k i ≤
        (∑ j, ((1 - c₀ j - c₁ j) * a Klo j + (1 - c₀ j) * a (Klo + 1) j + a (Klo + 2) j)
          + δbar) / (1 - c₀ i - c₁ i - c₂ i) := by sorry

end BotNguyenADMM.KL
