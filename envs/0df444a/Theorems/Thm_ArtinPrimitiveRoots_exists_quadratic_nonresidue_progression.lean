-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_exists_quadratic_nonresidue_progression
-- name    : ArtinPrimitiveRoots.exists_quadratic_nonresidue_progression
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T08:48:45.659784+00:00
-- url     : https://prove2.me/theorems/bd8ecbee-c832-41eb-ac06-0708b7e4100d
-- title:
--   Lemma 2.4 (OpenAI) — a progression of quadratic nonresidues meeting the conditions of Proposition 2.1
-- statement:
--   Let $a$ be an integer that is neither $-1$ nor a square, and set $M = 8\prod \ell$, the product over the odd primes $\ell$ dividing $a$. Then there are $c \in \{2, 4\}$ and an integer $u$ with
--
--   $$(u, M) = 1,\qquad c \mid u - 1,\qquad \bigl(\tfrac{u-1}{c}, \tfrac{M}{c}\bigr) = 1,$$
--
--   such that every prime $p \equiv u \pmod M$ satisfies $p \nmid a$ and $\left(\frac{a}{p}\right) = -1$.
--
--   The product runs over the prime factors of $|a|$ other than $2$. The Legendre symbol is Mathlib's `legendreSym p a`. As in Proposition 2.1 (`ArtinPrimitiveRoots.controlled_predecessors`), the coprimality conditions are `IsCoprime` over $\mathbb Z$ and the quotients are exact integer divisions.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 6: “Lemma 2.4 (A progression of quadratic nonresidues). Let $a \in \mathbb Z$ be neither $-1$ nor an integer square, and set $M = 8 \prod_{\ell \mid a,\ \ell \text{ odd prime}} \ell$. There are $c \in \{2, 4\}$ and an integer $u$ satisfying (2.1) such that every prime $p \equiv u \pmod M$ satisfies $p \nmid a$ and $(a/p) = -1$.” Condition (2.1), p. 5, is $(u, M) = 1$, $c \mid u - 1$, $\bigl(\frac{u-1}{c}, \frac{M}{c}\bigr) = 1$.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 6, Lemma 2.4

import Mathlib

namespace ArtinPrimitiveRoots

theorem exists_quadratic_nonresidue_progression (a : ℤ) (ha : a ≠ -1) (hsq : ¬ IsSquare a) :
    let M : ℕ := 8 * ∏ ℓ ∈ a.natAbs.primeFactors.filter (· ≠ 2), ℓ
    ∃ c : ℕ, (c = 2 ∨ c = 4) ∧ ∃ u : ℤ, IsCoprime u M ∧ (c : ℤ) ∣ u - 1 ∧
      IsCoprime ((u - 1) / c) ((M : ℤ) / c) ∧
      ∀ p : ℕ, (hp : p.Prime) → (p : ℤ) ≡ u [ZMOD M] →
        ¬ (p : ℤ) ∣ a ∧ @legendreSym p ⟨hp⟩ a = -1 := by
  sorry

end ArtinPrimitiveRoots
