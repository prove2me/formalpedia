-- Prove2me | Theorems.Thm_DirichletCharacters_zetaMul_prime_pow_eq
-- name    : DirichletCharacters.zetaMul_prime_pow_eq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:26:03.576984+00:00
-- url     : https://prove2.me/theorems/d7d99107-599d-4d0f-a982-6c0565642b1f
-- title:
--   The divisor-sum of a character at a prime power
-- statement:
--   **The local factor of $\zeta \star \chi$ at a prime power is a geometric sum.**
--
--   For a Dirichlet character $\chi$ and a prime $p$,
--
--   $$(\zeta \star \chi)(p^{k}) \;=\; \sum_{d \mid p^{k}} \chi(d) \;=\; \sum_{i=0}^{k} \chi(p)^{i}.$$
--
--   The divisors of $p^{k}$ are $1, p, \dots, p^{k}$, and $\chi$ is completely multiplicative on
--   prime powers, so $\chi(p^{i}) = \chi(p)^{i}$; the divisor sum therefore collapses to a finite
--   geometric series in the single value $\chi(p)$.
--
--   This computation is what makes $\zeta \star \chi$ tractable. When $\chi$ is **quadratic**,
--   $\chi(p) \in \{0,\pm1\}$ and the sum takes only the values $k+1$, $1$ or $0$ — in particular it
--   is always **non-negative**, which is precisely the positivity Landau's argument needs to rule
--   out a zero of $L(s,\chi)$ at $s = 1$. More generally it exhibits the Euler factor of
--   $\zeta(s)L(s,\chi)$ at $p$ as $\bigl((1-p^{-s})(1-\chi(p)p^{-s})\bigr)^{-1}$.
--
--   **Formalization note.** `DirichletCharacter.zetaMul χ` is Mathlib's name for the arithmetic
--   function $\zeta \star \chi$, i.e. $n \mapsto \sum_{d \mid n}\chi(d)$; the sum on the right runs
--   over $0 \le i \le k$.
-- source:
--   Classical; see Iwaniec & Kowalski, *Analytic Number Theory*, §5.9. Lean proof extracted from `Salt/SW/FourFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DirichletCharacters

open DirichletCharacter in
theorem zetaMul_prime_pow_eq {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    (k : ℕ) :
    χ.zetaMul (p ^ k) = ∑ i ∈ Finset.range (k + 1), (χ p) ^ i := by sorry

end DirichletCharacters
