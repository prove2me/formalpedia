-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_dirichlet_mean_value
-- name    : ArtinPrimitiveRoots.dirichlet_mean_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T19:59:15.475645+00:00
-- url     : https://prove2.me/theorems/057f20c8-0216-4590-ad59-9e293d143e8c
-- title:
--   The mean value theorem for Dirichlet polynomials, on intervals and with a Cauchy weight ([21] Lemma 2.2, (2.2))
-- statement:
--   Let $s$ be a finite set of integers in $[1, N]$ and $c : \mathbb N \to \mathbb C$, and put $P(t) = \sum_{n \in s}c_n n^{it}$. Then:
--
--   1. for all reals $T_1 \le T_2$, $\displaystyle\int_{T_1}^{T_2}|P(t)|^2\,dt \le \bigl(T_2 - T_1 + 4N(1 + \log N)\bigr)\sum_{n \in s}|c_n|^2$;
--   2. for every $a > 0$, $\displaystyle\int_{\mathbb R}\frac{|P(\tau)|^2}{1 + (\tau/a)^2}\,d\tau \le \bigl(\pi a + 2\pi N(1 + \log N)\bigr)\sum_{n \in s}|c_n|^2$.
--
--   A step in the proof of Lemma 10.2's major-term bound `major_square_bound`, through OpenAI's *The Poisson–Dirichlet law for prime predecessors*, where it is the mean-square part of Lemma 2.2. The constants are explicit.
--
--   OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 6, Lemma 2.2: “Let $P(t) = \sum_{n \le Y}c_nn^{it}$. On every real interval $I$ of length $T \ge 0$, $\int_I|P(t)|^2\,dt \ll (T + Y\log(2Y))\sum_n|c_n|^2$. (2.2)”
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 6, Lemma 2.2, the mean value theorem for Dirichlet polynomials (2.2), plain and with a Cauchy weight, as used in the proof of Proposition 5.1

import Mathlib

namespace ArtinPrimitiveRoots

open Real

theorem dirichlet_mean_value (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (c : ℕ → ℂ) :
    (∀ T₁ T₂ : ℝ, T₁ ≤ T₂ →
      ∫ t in T₁..T₂, ‖∑ n ∈ s, c n * (n : ℂ) ^ (Complex.I * t)‖ ^ 2 ≤
        (T₂ - T₁ + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2) ∧
    (∀ a : ℝ, 0 < a →
      ∫ τ, (1 + (τ / a) ^ 2)⁻¹ * ‖∑ n ∈ s, c n * (n : ℂ) ^ (Complex.I * τ)‖ ^ 2 ≤
        (π * a + 2 * π * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2) := by
  sorry

end ArtinPrimitiveRoots
