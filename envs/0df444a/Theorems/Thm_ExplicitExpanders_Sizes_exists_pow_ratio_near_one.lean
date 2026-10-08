-- Prove2me | Theorems.Thm_ExplicitExpanders_Sizes_exists_pow_ratio_near_one
-- name    : ExplicitExpanders.Sizes.exists_pow_ratio_near_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:37.746889+00:00
-- url     : https://prove2.me/theorems/db7ec1c5-0980-43ae-8cf4-c2033f29ed66
-- title:
--   Proof of Lemma 2.2 — $1\le q_1^{k_1}/q_2^{k_2}\le 1+\mu$ with $k_1\ge1$
-- statement:
--   Let $q_1$ and $q_2$ be distinct prime numbers and let $\mu>0$. Then there are integers $k_1\ge1$ and $k_2\ge0$ such that
--
--   $$
--   1\le\frac{q_1^{k_1}}{q_2^{k_2}}\le 1+\mu .
--   $$
--
--   This is the displayed inequality in the proof of Lemma 2.2. In the paper it comes with an intermediate bound $q_1^{k_1}/q_2^{k_2}\le q_2^{\delta}\le 1+\mu$, where $\delta>0$ is chosen small enough that $q_2^{\delta}\le 1+\mu$. Replacing $q_1^{k_1}$ by $q_2^{k_2}$ changes a number by a factor close to $1$, and this is the step that drives Lemma 2.2.
--
--   **Formalization Note** The requirement $k_1\ge1$ is part of the statement: with $k_1=k_2=0$ the inequality would hold trivially. Since $q_1^{k_1}\ne q_2^{k_2}$ for $k_1\ge1$ by unique factorisation, the lower bound is in fact strict for every witness. The quotient is computed in $\mathbb R$.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 7, proof of Lemma 2.2 (displayed inequality)

import Mathlib

namespace ExplicitExpanders.Sizes

/-- Proof of Lemma 2.2 (arXiv:2003.11673v1, p. 7), display: for distinct primes `q₁, q₂` and every
`μ > 0` there are integers `k₁ ≥ 1`, `k₂ ≥ 0` with `1 ≤ q₁^{k₁} / q₂^{k₂} ≤ 1 + μ`. -/
theorem exists_pow_ratio_near_one {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 1 ≤ (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ∧
      (q₁ : ℝ) ^ k₁ / (q₂ : ℝ) ^ k₂ ≤ 1 + μ := by sorry

end ExplicitExpanders.Sizes
