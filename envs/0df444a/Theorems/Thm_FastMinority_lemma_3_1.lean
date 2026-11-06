-- Prove2me | Theorems.Thm_FastMinority_lemma_3_1
-- name    : FastMinority.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:04:29.780769+00:00
-- url     : https://prove2.me/theorems/cd9a3f67-7dcf-4b4f-870b-559abb36ad1b
-- title:
--   Lemma 3.1 — weighted hitting-time bound: $T_{S_2}=O((\log(1+p_{\max}W)+\ell)/(1-\lambda))$ w.p. $\ge1-2^{-\ell}$
-- statement:
--   Let $(Z_t)_{t\ge0}$ be a Markov chain on a finite state space $S=S_1\,\dot\cup\,S_2$ with transition probabilities $K(i,j)$, and let $T_{S_2}=\inf\{t\ge0:Z_t\in S_2\}$. Suppose there are positive weights $(w_i)_{i\in S_1}$ and a constant $0<\lambda<1$ with
--   $$
--   \sum_{i\in S_1}w_i\,K(i,j)\le\lambda\,w_j\qquad\text{for every }j\in S_1. \tag{3.2}
--   $$
--   Let $p_i=\Pr(Z_0=i)$, $p_{\max}=\max_{i\in S_1}p_i$ and $W=\sum_{i\in S_1}w_i/\min_{i\in S_1}w_i$. Then there is an absolute constant $C>0$ such that for every integer $\ell\ge1$,
--   $$
--   \Pr\Big[T_{S_2}\le C\,\frac{\log(1+p_{\max}W)+\ell}{1-\lambda}\Big]\ge1-2^{-\ell}.
--   $$
--
--   The lemma turns a weighted sub-invariance of the killed kernel into a tail bound for the hitting time; the source applies it with $w_i=1/i$ and $\lambda=3/4$ (Proposition 3.7).
--
--   **Formalization Note** $S_1$ is a nonempty finite set of states of a finite type and $S_2$ its complement; the chain is given by a stochastic matrix and the initial law by a probability vector. The probability of $T_{S_2}>t$ is written with `avoidProb`.
--
--   Differences from the source:
--   - reading: T_{S₂} = O((log(1 + p_max W) + ℓ)/(1 − λ)) with probability ≥ 1 − 2^{−ℓ} → ∃ C > 0 chosen before the chain, weights, λ, initial law and ℓ, with Pr(T_{S₂} > ⌊C·(log(1 + p_max W) + ℓ)/(1 − λ)⌋) ≤ 2^{−ℓ}; reason: the O is uniform (the A.4 proof gives an explicit t_ℓ); T is an integer, so T ≤ u iff T ≤ ⌊u⌋
--   - encoding: finite state space S = S₁ ∪̇ S₂, K(i, j) the transition probabilities → a finite type α with a stochastic matrix P, S₁ a nonempty Finset, S₂ = S₁ᶜ; reason: max and min over S₁ are undefined for S₁ = ∅ (and then T = 0)
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 3.1, p.7 (PDF p.9); proof in Appendix A.4, p.44 (PDF p.46)

import Mathlib
import Definitions.Def_MinorityDynamics_Kernel

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Lemma 3.1** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.7 = PDF p.9; proof in Appendix A.4, p.44 = PDF p.46): a weighted
hitting-time bound for a finite Markov chain. Let `Z` be a Markov chain with transition matrix `P` on
a finite state space `S = S₁ ∪ S₂` (disjoint), `T_{S₂} = inf{t ≥ 0 : Z_t ∈ S₂}`, positive weights
`(w_i)_{i ∈ S₁}` and `0 < λ < 1` with `∑_{i ∈ S₁} w_i K(i, j) ≤ λ w_j` for every `j ∈ S₁` (3.2). With
`p_i = Pr(Z₀ = i)`, `p_max = max_{i ∈ S₁} p_i` and `W = ∑_{i ∈ S₁} w_i / min_{i ∈ S₁} w_i`, for
every integer `ℓ ≥ 1`, with probability at least `1 − 2^{−ℓ}`,
`T_{S₂} = O((log(1 + p_max W) + ℓ)/(1 − λ))`.

**Formalization Note** `S₂` is the complement of the finite set `S₁` (assumed nonempty, so that the
maximum and the minimum exist). `K(i, j)` is `P i j` for `i, j ∈ S₁`. `Pr(T_{S₂} > t)` for the initial
law `p` is `∑ₓ p x · avoidProb P S₂ t x`. The `O(·)` is an absolute constant `C`, chosen before the
chain, the weights, `λ`, `p` and `ℓ`; "`T ≤ C·u`" is "`T ≤ ⌊C·u⌋`" since `T` is an integer. -/
theorem lemma_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type} [Fintype α] (P : α → α → ℝ), (∀ x y, 0 ≤ P x y) →
      (∀ x, ∑ y, P x y = 1) → ∀ (S₁ : Finset α) (hS : S₁.Nonempty) (w : α → ℝ),
      (∀ i ∈ S₁, 0 < w i) → ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ j ∈ S₁, ∑ i ∈ S₁, w i * P i j ≤ lam * w j) →
      ∀ p : α → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∑ x, p x * MinorityDynamics.avoidProb P (↑S₁ : Set α)ᶜ
          ⌊C * (Real.log (1 + S₁.sup' hS p * ((∑ i ∈ S₁, w i) / S₁.inf' hS w)) + ℓ) /
            (1 - lam)⌋₊ x ≤ (2 : ℝ) ^ (-(ℓ : ℤ)) := by sorry

end FastMinority
