-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_controlled_predecessors
-- name    : ArtinPrimitiveRoots.controlled_predecessors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T08:48:54.20975+00:00
-- url     : https://prove2.me/theorems/d17b9cd2-c649-4466-b78d-db09ed653f58
-- title:
--   Proposition 2.1 (OpenAI) — primes with controlled predecessors in a fixed progression
-- statement:
--   Let $M$ be a positive multiple of $8$, let $c \in \{2, 4\}$, and let $u$ be an integer with
--
--   $$(u, M) = 1,\qquad c \mid u - 1,\qquad \bigl(\tfrac{u-1}{c}, \tfrac{M}{c}\bigr) = 1.$$
--
--   Then there are $C > 0$ and $x_0$ such that for every real $x \ge x_0$, writing $L = \log x$, at least $C x / L^2$ primes $p$ with $x < p < 2x$ satisfy
--
--   $$p \equiv u \pmod M,\qquad p - 1 = c\,r\,Q,$$
--
--   where $Q > x^{0.9}$ is prime and $r$ is a positive integer all of whose prime factors $\ell$ satisfy $\exp(L^{0.1}) < \ell < \exp(L^{0.3})$.
--
--   The constants $C$ and $x_0$ depend on $M$, $c$ and $u$. Both coprimality conditions are stated as `IsCoprime` over $\mathbb Z$, and the quotients $(u-1)/c$ and $M/c$ are exact integer divisions, since $c$ divides both.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 5: “Proposition 2.1 (Primes with controlled predecessors). Let $M$ be a fixed positive multiple of 8, let $c \in \{2, 4\}$, and let $u$ be an integer satisfying $(u, M) = 1$, $c \mid u - 1$, $\bigl(\frac{u-1}{c}, \frac{M}{c}\bigr) = 1$. (2.1) For every sufficiently large real $x$, there are $\gg_{M,c,u} x/L^2$ distinct primes $p \in (x, 2x)$ satisfying $p \equiv u \pmod M$, $p - 1 = crQ$, $Q > x^{0.9}$ prime, (2.2) where $r$ is a positive integer all of whose prime divisors lie in $(\exp(L^{0.1}), \exp(L^{0.3}))$.” The paper proves it in §12, using Bombieri–Vinogradov, a Brun–Hooley block sieve and rough-number densities.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 5, Proposition 2.1

import Mathlib

namespace ArtinPrimitiveRoots

theorem controlled_predecessors (M c : ℕ) (u : ℤ) (hM : 0 < M) (h8 : 8 ∣ M)
    (hc : c = 2 ∨ c = 4) (hu : IsCoprime u M) (hcu : (c : ℤ) ∣ u - 1)
    (hcop : IsCoprime ((u - 1) / c) ((M : ℤ) / c)) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      C * x / Real.log x ^ 2 ≤
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ (p : ℤ) ≡ u [ZMOD M] ∧
          ∃ r Q : ℕ, p - 1 = c * r * Q ∧ Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ 0 < r ∧
            ∀ ℓ ∈ r.primeFactors, Real.exp (Real.log x ^ (0.1 : ℝ)) < ℓ ∧
              (ℓ : ℝ) < Real.exp (Real.log x ^ (0.3 : ℝ))} : ℝ) := by
  sorry

end ArtinPrimitiveRoots
