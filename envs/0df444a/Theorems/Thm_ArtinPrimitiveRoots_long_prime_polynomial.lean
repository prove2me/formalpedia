-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_long_prime_polynomial
-- name    : ArtinPrimitiveRoots.long_prime_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T12:51:27.589977+00:00
-- url     : https://prove2.me/theorems/b1db725d-7d55-4bd8-a2a2-afd9d365d23f
-- title:
--   Lemma 3.1 of OpenAI's Prime Predecessors paper — the long prime polynomial, Σ_{p∈I} χ(p) p^{−1+it} ≪ L^{−A} for L^{B₀} ≤ |t| ≤ x²
-- statement:
--   Fix $0 < \tau < \eta < 1$, $C > 0$ and $A > 0$, and write $L = \log x$. There are $B_0$, $K$ and $x_0$ such that for every $x \ge x_0$, every real $N$ with $x^\tau/2 \le N \le x^\eta$, every integer $q$ with $1 \le q \le L^C$, every Dirichlet character $\chi$ modulo $q$, every real $t$ with $L^{B_0} \le |t| \le x^2$, and every interval $J \subseteq [N, 2N]$,
--
--   $$\Bigl|\sum_{p \in J} \chi(p)\,p^{-1+it}\Bigr| \le K L^{-A},$$
--
--   the sum running over primes. $B_0$, $K$ and $x_0$ depend only on $\tau, \eta, C, A$.
--
--   This is a result of OpenAI's companion paper, taken here as an input. That paper proves it by Vinogradov's mean value method, a zero-free strip for Dirichlet $L$-functions at large height, and Mellin inversion (§3, pp. 4–11). The primitive-roots paper applies it as (10.18) in the proof of Proposition 10.3 (p. 69). The same estimate, with the same ranges, is Lemma 2.3 of OpenAI's *The Poisson–Dirichlet law for prime predecessors*.
--
--   **Formalization note.** A Dirichlet character is Mathlib's `DirichletCharacter ℂ q`, extended by zero on nonunits. "An interval $I \subset [N, 2N]$" is any order-connected set $J \subseteq [N, 2N]$ (renamed because `I` is the imaginary unit), and "$q \le L^C$" is read as $1 \le q \le L^C$. The implicit constant of $\ll$ is the explicit $K$, and the estimate is asserted for $x \ge x_0$.
--
--   OpenAI, *Prime Predecessors with an Even Number of Prime Factors* (2026), p. 4: “Throughout this section, $L = \log x$ and $T = \log L$. Lemma 3.1 (Long prime polynomial). Fix $0 < \tau < \eta < 1$, $C > 0$, and $A > 0$. There is a constant $B_0 = B_0(\tau, \eta, C, A)$ such that, uniformly for $\frac{x^\tau}{2} \le N \le x^\eta$, $q \le L^C$, $L^{B_0} \le |t| \le x^2$, every Dirichlet character $\chi$ modulo $q$ and every interval $I \subset [N, 2N]$ satisfy $\Bigl|\sum_{p \in I}\chi(p)p^{-1+it}\Bigr| \ll_{\tau,\eta,C,A} L^{-A}$. (3.1)”
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 69: “For the remaining frequencies, use the long prime polynomial estimate [22, Lemma 3.1] and the corresponding bound for the small-prime proxy.”
-- source:
--   OpenAI, Prime Predecessors with an Even Number of Prime Factors, OpenAI Math Release preprint, September 17, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf (Apache-2.0), p. 4, Lemma 3.1 (long prime polynomial), as applied in (10.18) of the primitive-roots paper (p. 69)

import Mathlib

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem long_prime_polynomial (τ η C A : ℝ) (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ B₀ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ N : ℝ, x ^ τ / 2 ≤ N → N ≤ x ^ η →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ log x ^ C → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, log x ^ B₀ ≤ |t| → |t| ≤ x ^ 2 →
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc N (2 * N) →
        ‖∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter Nat.Prime,
            (if (p : ℝ) ∈ J then χ (p : ZMod q) * (p : ℂ) ^ (-1 + Complex.I * t) else 0)‖ ≤
          K * log x ^ (-A) := by
  sorry

end ArtinPrimitiveRoots
