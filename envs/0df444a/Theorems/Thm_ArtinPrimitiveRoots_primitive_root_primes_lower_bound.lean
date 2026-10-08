-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_primitive_root_primes_lower_bound
-- name    : ArtinPrimitiveRoots.primitive_root_primes_lower_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T08:48:53.635474+00:00
-- url     : https://prove2.me/theorems/8a19c512-5a65-4a1f-b516-c619da4d12cd
-- title:
--   Theorem 1.1 (OpenAI) — every admissible integer is a primitive root modulo ≫ x/(log x)² primes in (x, 2x)
-- statement:
--   Let $a$ be an integer that is neither $-1$ nor a square. Then there are constants $c > 0$ and $x_0 \ge 2$ such that for every real $x \ge x_0$,
--
--   $$\#\{p \text{ prime} : x < p < 2x,\ p \nmid a,\ \operatorname{ord}_p(a) = p - 1\} \ \ge\ c\,\frac{x}{(\log x)^2}.$$
--
--   Here $\operatorname{ord}_p(a)$ is the multiplicative order of $a$ modulo $p$, written `orderOf (a : ZMod p)`; the count is the cardinality (`Nat.card`) of the set of such primes. In particular $a$ is a primitive root modulo infinitely many primes, which is the infinitude assertion of Artin's primitive root conjecture.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 2: “Theorem 1.1. For every admissible integer $a$, there are constants $c_a > 0$ and $x_a \ge 2$ such that, for every real $x \ge x_a$, $\#\{p \text{ prime} : x < p < 2x,\ p \nmid a,\ \operatorname{ord}_p(a) = p - 1\} \ge c_a \frac{x}{(\log x)^2}$.” Admissible is defined on p. 2: “Call $a$ admissible if $a \ne -1$ and $a$ is not the square of an integer.”
--
--   The paper proves it in §2 (pp. 5–7) from Proposition 2.1 (primes with controlled predecessors, `ArtinPrimitiveRoots.controlled_predecessors`), Proposition 2.2 (a uniform bound for complete splitting in Kummer fields, `ArtinPrimitiveRoots.uniform_splitting_bound`) and Lemma 2.4 (a progression of quadratic nonresidues, `ArtinPrimitiveRoots.exists_quadratic_nonresidue_progression`). OpenAI has published no Lean for this paper.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 2, Theorem 1.1

import Mathlib

namespace ArtinPrimitiveRoots

theorem primitive_root_primes_lower_bound (a : ℤ) (ha : a ≠ -1) (hsq : ¬ IsSquare a) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ^ 2 ≤
        (Nat.card {p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < 2 * x ∧ ¬ (p : ℤ) ∣ a ∧
          orderOf (a : ZMod p) = p - 1} : ℝ) := by
  sorry

end ArtinPrimitiveRoots
