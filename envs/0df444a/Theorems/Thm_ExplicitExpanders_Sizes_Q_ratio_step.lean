-- Prove2me | Theorems.Thm_ExplicitExpanders_Sizes_Q_ratio_step
-- name    : ExplicitExpanders.Sizes.Q_ratio_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:33:45.126165+00:00
-- url     : https://prove2.me/theorems/9eb3e697-3335-4080-8d1d-9b2515db3481
-- title:
--   Proof of Lemma 2.2 — $Q(q_1,q_2,s,t)/Q(q_1,q_2,s-k_1,t+k_2)\in[1,(1+\mu)^3]$ (typo corrected)
-- statement:
--   Let $q_1$ and $q_2$ be distinct primes, let $\mu>0$, and let $k_1\ge1$ and $k_2\ge0$ be integers with
--
--   $$
--   1\le\frac{q_1^{k_1}}{q_2^{k_2}}\le 1+\mu .
--   $$
--
--   Then for all integers $s>k_1$ and $t\ge1$,
--
--   $$
--   1\le\frac{Q(q_1,q_2,s,t)}{Q(q_1,q_2,s-k_1,t+k_2)}\le(1+\mu)^3 ,
--   $$
--
--   where $Q$ is the LPS vertex count $Q(q_1,q_2,s,t)=q_1^{3(s-1)}q_2^{3(t-1)}\frac{q_1(q_1-1)(q_1+1)}{2}\frac{q_2(q_2-1)(q_2+1)}{2}$.
--
--   This is the last sentence of the proof of Lemma 2.2, with a misprint corrected. Moving from $(s,t)$ to $(s-k_1,t+k_2)$ divides $Q$ by a factor in $[1,(1+\mu)^3]$, so a chain of such moves passes through every interval $[n,(1+\mu)^3n]$ with $n$ large.
--
--   **Formalization Note** The paper prints $Q(q_1,q_2,s-k_1,t-k_2)$ and "$s,t\ge\max\{k_1,k_2\}$". As printed the sentence is false: $Q(q_1,q_2,s,t)/Q(q_1,q_2,s-k_1,t-k_2)=q_1^{3k_1}q_2^{3k_2}$, which is large. The intended pair is $(s-k_1,t+k_2)$, for which the ratio is $(q_1^{k_1}/q_2^{k_2})^3$. The index conditions are adjusted: $s>k_1$ makes $s-k_1$ positive, and $t\ge1$; no lower bound on $t$ in terms of $k_2$ is needed after correcting the sign. Distinctness, $\mu>0$, and $k_1>0$ are retained from the proof even though the algebraic identity alone needs none of them. The ratio is computed in $\mathbb R$ after casting the natural numbers $Q(\cdot)$.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 7, proof of Lemma 2.2 (last sentence; printed t − k2 corrected to t + k2)

import Mathlib
import Definitions.Def_ExplicitExpanders_Sizes_Q

namespace ExplicitExpanders.Sizes

/-- Proof of Lemma 2.2 (arXiv:2003.11673v1, p. 7), last sentence, with the printed
`Q(q₁, q₂, s − k₁, t − k₂)` corrected to `Q(q₁, q₂, s − k₁, t + k₂)`: if
for distinct primes, `μ > 0`, `k₁ > 0`, and `1 ≤ q₁^{k₁} / q₂^{k₂} ≤ 1 + μ`, then for all
`s > k₁` and `t ≥ 1` the ratio between
`Q(q₁, q₂, s, t)` and `Q(q₁, q₂, s − k₁, t + k₂)` lies between `1` and `(1 + μ)³`. -/
theorem Q_ratio_step {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    {μ : ℝ} (hμ : 0 < μ) {k₁ k₂ : ℕ} (hk₁ : 0 < k₁)
    (hlow : 1 ≤ (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂) (hupp : (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ≤ 1 + μ)
    {s t : ℕ} (hs : k₁ < s) (ht : 1 ≤ t) :
    1 ≤ (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ∧
      (Q q₁ q₂ s t : ℝ) / (Q q₁ q₂ (s - k₁) (t + k₂) : ℝ) ≤ (1 + μ) ^ 3 := by sorry

end ExplicitExpanders.Sizes
