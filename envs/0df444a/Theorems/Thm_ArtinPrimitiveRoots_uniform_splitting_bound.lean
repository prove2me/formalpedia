-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_uniform_splitting_bound
-- name    : ArtinPrimitiveRoots.uniform_splitting_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T08:49:17.598735+00:00
-- url     : https://prove2.me/theorems/c639cb83-dbe6-4862-9421-33d9fba65d2d
-- title:
--   Proposition 2.2 (OpenAI, elementary form) — uniform bound for complete splitting in the Kummer fields ℚ(μ_q, a^{1/q})
-- statement:
--   Let $a$ be an integer with $|a| > 1$, and put $\delta_0 = 10^{-6}$ and $L = \log x$. There are $C > 0$, $q_0$ and $x_0$ such that for every real $x \ge x_0$ and every prime $q$ with $q_0 \le q \le \exp(L^{0.3})$,
--
--   $$\#\{p \text{ prime} : x < p \le 2x,\ p \nmid aq,\ p \equiv 1 \!\!\pmod q,\ a^{(p-1)/q} \equiv 1 \!\!\pmod p\} \ \le\ C\Bigl(\frac{x}{q(q-1)L} + x^{1-\delta_0}\Bigr).$$
--
--   $C$, $q_0$ and $x_0$ depend only on $a$, not on $q$. Moreover, for $a = 2$ the same holds for every prime $q \ge 5$ (that is, with $q_0 = 5$).
--
--   **Formalization note.** The paper counts the primes $p \in (x, 2x]$ that split completely in $K_q = \mathbb Q(\mu_q, a^{1/q})$. This statement counts instead the primes $p \nmid aq$ satisfying the two congruences that, by the paper's Lemma 2.3 (p. 6), characterise complete splitting for $p \nmid aq$. Every prime counted here splits completely in $K_q$, so this statement follows from the printed one; it is the form the proof of Theorem 1.1 uses. The congruence $a^{(p-1)/q} \equiv 1$ is written in `ZMod p`, with the exponent a natural-number quotient that is exact when $p \equiv 1 \pmod q$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 6: “Proposition 2.2 (Uniform bound for complete splitting). Fix an integer $a$ with $|a| > 1$, and put $\delta_0 = 10^{-6}$. For all sufficiently large real $x$ and all primes $q$ sufficiently large in terms of $a$, with $q \le \exp(L^{0.3})$, one has $\#\{p \text{ prime} : x < p \le 2x,\ p \text{ splits completely in } K_q\} \ll_a \frac{x}{q(q-1)L} + x^{1-\delta_0}$. (2.4) The implied constant and the threshold for $x$ are independent of $q$. For $a = 2$, every prime $q \ge 5$ is allowed, with absolute constants and an absolute threshold for $x$.” And p. 6: “Lemma 2.3 (Splitting test). Let $a \ne 0$ be an integer, and let $p, q$ be primes with $p \nmid aq$. Then $p$ splits completely in $K_q$ if and only if $p \equiv 1 \pmod q$, $a^{(p-1)/q} \equiv 1 \pmod p$.” The paper proves Proposition 2.2 in §9 from its Hecke zero-free theorem (Theorem 1.2).
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 6, Proposition 2.2, in the elementary form given by Lemma 2.3 (p. 6)

import Mathlib

namespace ArtinPrimitiveRoots

theorem uniform_splitting_bound (a : ℤ) (ha : 1 < |a|) :
    (∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → q₀ ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (0.3 : ℝ)) →
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
            p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} : ℝ) ≤
          C * (x / (q * (q - 1) * Real.log x) + x ^ (1 - (1 / 10 ^ 6 : ℝ)))) ∧
    (a = 2 → ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, q.Prime → 5 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.log x ^ (0.3 : ℝ)) →
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) ≤ 2 * x ∧ ¬ (p : ℤ) ∣ a * q ∧
            p ≡ 1 [MOD q] ∧ (a : ZMod p) ^ ((p - 1) / q) = 1} : ℝ) ≤
          C * (x / (q * (q - 1) * Real.log x) + x ^ (1 - (1 / 10 ^ 6 : ℝ)))) := by
  sorry

end ArtinPrimitiveRoots
