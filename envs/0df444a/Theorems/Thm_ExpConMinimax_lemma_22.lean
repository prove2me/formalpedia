-- Prove2me | Theorems.Thm_ExpConMinimax_lemma_22
-- name    : ExpConMinimax.lemma_22
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:49:46.884877+00:00
-- url     : https://prove2.me/theorems/dff8d487-f46c-4a48-8863-4fd2e5ba57fa
-- title:
--   Lemma 22 — discrete Grönwall bound $a_K\le b_1(1+b_2)^K$
-- statement:
--   Let $(a_t)_{t\ge0}$ be a nonnegative real sequence and $b_1,b_2\ge0$ with $a_0\le b_1$. If
--   $$a_K\le b_1+b_2\sum_{t=0}^{K-1}a_t\qquad\text{for all }K\ge1,$$
--   then
--   $$a_K\le b_1(1+b_2)^K\qquad\text{for all }K\ge1 .$$
--
--   In the paper this turns the recursive bound on $\mathbb E\|\lambda_K\|^2+\mathbb E\|\gamma_K\|^2$ into the uniform bound of Proposition 7 (with $b_2=2/N$ and $K\le N$).
--
--   Differences from the source: none.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, Lemma 22, p.31 (quoted from Lemma 2.8 of reference [7])

import Mathlib

namespace ExpConMinimax

/-- **Lemma 22** (discrete Grönwall bound).
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, Lemma 22, p.31 (quoted from Lemma 2.8 of reference [7]):

"Let `{aₜ}_{t≥0}` be a nonnegative sequence and `b₁, b₂ ≥ 0` be two constants such that
`a₀ ≤ b₁`. Suppose for all `K ≥ 1`, it holds that `a_K ≤ b₁ + b₂ ∑_{t=0}^{K−1} aₜ`. Then we have
`a_K ≤ b₁(1 + b₂)^K` for all `K ≥ 1`." -/
theorem lemma_22 (a : ℕ → ℝ) (b₁ b₂ : ℝ) (ha : ∀ t, 0 ≤ a t) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (ha₀ : a 0 ≤ b₁)
    (hrec : ∀ K, 1 ≤ K → a K ≤ b₁ + b₂ * ∑ t ∈ Finset.range K, a t) :
    ∀ K, 1 ≤ K → a K ≤ b₁ * (1 + b₂) ^ K := by sorry

end ExpConMinimax
