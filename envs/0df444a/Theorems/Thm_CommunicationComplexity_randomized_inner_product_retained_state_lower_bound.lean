-- Prove2me | Theorems.Thm_CommunicationComplexity_randomized_inner_product_retained_state_lower_bound
-- name    : CommunicationComplexity.randomized_inner_product_retained_state_lower_bound
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T18:29:35.175599+00:00
-- url     : https://prove2.me/theorems/1e08bb63-f60f-5739-965a-26d842458b5a
-- title:
--   One-pass memory lower bound for binary inner product
-- statement:
--   Let $X$ and $Y$ be independent uniform $m$-bit blocks, with $X$ arriving first. Fix any finite set $S$ of retained states and any finite distribution of random seeds independent of $X,Y$. For each seed, the first stage maps $X$ to a state in $S$. The second stage uses the seed, that state, and $Y$ to predict the parity of $\sum_{i=1}^m X_iY_i$. If the average success probability is at least $2/3$, then $2^m\leq 9|S|$.
-- source:
--   Adaptation of the Hadamard orthogonality and Cauchy–Schwarz method for binary inner product in Benny Chor and Oded Goldreich, Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity, SIAM Journal on Computing 17(2), 1988, Theorem 9, https://doi.org/10.1137/0217015.

import Mathlib

open scoped BigOperators

theorem CommunicationComplexity.randomized_inner_product_retained_state_lower_bound {m : ℕ} {State Seed : Type} [Fintype State] [Fintype Seed]
    (retain : Seed → (Fin m → Bool) → State)
    (reply : Seed → State → (Fin m → Bool) → Bool)
    (weight : Seed → ℝ) (nonneg : ∀ r, 0 ≤ weight r) (total : (∑ r, weight r) = 1)
    (good : (2 : ℝ) / 3 ≤ ∑ r, weight r *
      ((∑ x : Fin m → Bool, ∑ y : Fin m → Bool,
        if reply r (retain r x) y = decide (Odd (∑ i : Fin m, (x i && y i).toNat))
        then 1 else 0) / ((2 : ℝ) ^ m) ^ 2)) :
    2 ^ m ≤ 9 * Fintype.card State := by sorry
