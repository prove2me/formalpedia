-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_small_prime_sparse_mean
-- name    : ArtinPrimitiveRoots.small_prime_sparse_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T19:59:27.589355+00:00
-- url     : https://prove2.me/theorems/0c404dc6-403a-4bfd-b94b-33636c8bcdd3
-- title:
--   [21] Lemma 5.3 as used for (5.22) — a polynomial over primes near P ≈ exp(L^{0.1…0.2}) saves any power of log x in a weighted mean square
-- statement:
--   Fix $\delta, C, A_s > 0$ and write $L = \log x$. There is $x_0$ such that for every $x \ge x_0$ the following holds. Take $H_n$ with $x^\delta \le H_n \le x$, coefficients $|c_n| \le L^C$, and $P \ge 2$ with $L^{0.1} \le \log P \le 3L^{0.2}$. Let $\mathcal S$ be a set of primes in $[P, 2P]$, and $0 \le Z \le x^3$. Let $M$ be a continuous function with $|M(\tau)| \le \varepsilon_M$ on $[-Z, Z]$. Then, with $N(\tau) = \sum_{H_n \le n \le 2H_n}c_nn^{i\tau}$,
--
--   $$\int_{-Z}^{Z}\Bigl|\frac1P\sum_{p \in \mathcal S}p^{i\tau}\Bigr|^2|M(\tau)|^2|N(\tau)|^2\,d\tau \le L^{-2A_s}\int_{-Z}^{Z}|M(\tau)|^2|N(\tau)|^2\,d\tau + 1800\,\varepsilon_M^2H_n^2L^{2C+1}.$$
--
--   A step in the proof of Lemma 10.2's major-term bound `major_square_bound`: the form of [21, Lemma 5.3] used in (5.22) of OpenAI's *The Poisson–Dirichlet law for prime predecessors*, with explicit constants.
--
--   **Formalization note.** The second term is written $4\varepsilon_M^2\cdot 450H_n^2L^{2C+1}$ in the Lean.
--
--   OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 35: “Lemma 5.3 (A small prime factor and sparse frequencies). Let $P$ satisfy $cL^{0.1} \le \log P \le C_1L^{0.2}$, […]”
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 35, Lemma 5.3 (a small prime factor and sparse frequencies), in the form used for (5.22)

import Mathlib

namespace ArtinPrimitiveRoots

open Real

theorem small_prime_sparse_mean (δ C As : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hAs : 0 < As) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Hn : ℝ, x ^ δ ≤ Hn → Hn ≤ x →
      ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ Real.log x ^ C) →
      ∀ P : ℝ, 2 ≤ P → Real.log x ^ (0.1 : ℝ) ≤ Real.log P →
      Real.log P ≤ 3 * Real.log x ^ (0.2 : ℝ) →
      ∀ 𝒮 : Finset ℕ, (∀ p ∈ 𝒮, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Z : ℝ, 0 ≤ Z → Z ≤ x ^ 3 →
      ∀ M : ℝ → ℂ, Continuous M → ∀ εM : ℝ, (∀ τ : ℝ, |τ| ≤ Z → ‖M τ‖ ≤ εM) →
      ∫ τ in (-Z)..Z, ‖((P : ℂ))⁻¹ * ∑ p ∈ 𝒮, (p : ℂ) ^ (Complex.I * τ)‖ ^ 2 * ‖M τ‖ ^ 2 *
          ‖∑ n ∈ (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ => Hn ≤ (n : ℝ)),
            c n * (n : ℂ) ^ (Complex.I * τ)‖ ^ 2 ≤
        (Real.log x ^ (-As)) ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 *
          ‖∑ n ∈ (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n : ℕ => Hn ≤ (n : ℝ)),
            c n * (n : ℂ) ^ (Complex.I * τ)‖ ^ 2) +
        4 * εM ^ 2 * (450 * Hn ^ 2 * Real.log x ^ (2 * C + 1)) := by
  sorry

end ArtinPrimitiveRoots
