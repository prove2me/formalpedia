-- Prove2me | Theorems.Thm_CondatPD_FinDim_lemma_4_6
-- name    : CondatPD.FinDim.lemma_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:19:37.72011+00:00
-- url     : https://prove2.me/theorems/d6eea57f-dd15-4197-9141-21be190ce73c
-- title:
--   Lemma 4.6 (Polyak), p. 10 — aₙ₊₁ ≤ cₙaₙ + bₙ with Σ(1 − cₙ) = +∞ and bₙ/(1 − cₙ) → 0 forces aₙ → 0
-- statement:
--   Let $(a_n)$, $(b_n)$, $(c_n)$ be sequences of reals such that
--
--   1. $0\le a_n$, $0\le c_n<1$ and $0\le b_n$ for every $n$;
--   2. $a_{n+1}\le c_na_n+b_n$ for every $n$;
--   3. $\sum_{n\in\mathbb N}(1-c_n)=+\infty$;
--   4. $b_n/(1-c_n)\to0$.
--
--   Then
--   $$a_n\to0 .$$
--
--   In the proof of Theorem 3.3 it is applied with $a_n=\|z_n-\hat z\|$, $b_n=\rho_n\|\tilde z_{n+1}-\hat z\|$, $c_n=|1-\rho_n|$ to pass from the convergence of $(\tilde z_n)$ to that of the iterates $(z_n)$.
--
--   **Formalization Note** Condition 3 is stated as divergence of the partial sums to $+\infty$; the division in condition 4 is well defined because $c_n<1$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 10, Lemma 4.6

import Mathlib

open Filter Topology

namespace CondatPD.FinDim

/-- Lemma 4.6 (Polyak), p. 10: if `0 ≤ aₙ`, `0 ≤ cₙ < 1`, `0 ≤ bₙ`, `aₙ₊₁ ≤ cₙ aₙ + bₙ`,
`Σ (1 − cₙ) = +∞` and `bₙ/(1 − cₙ) → 0`, then `aₙ → 0`. -/
theorem lemma_4_6 (a b c : ℕ → ℝ)
    (h1 : ∀ n, 0 ≤ a n ∧ 0 ≤ c n ∧ c n < 1 ∧ 0 ≤ b n)
    (h2 : ∀ n, a (n + 1) ≤ c n * a n + b n)
    (h3 : Tendsto (fun N => ∑ n ∈ Finset.range N, (1 - c n)) atTop atTop)
    (h4 : Tendsto (fun n => b n / (1 - c n)) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by sorry

end CondatPD.FinDim
