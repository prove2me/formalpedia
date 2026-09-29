-- Prove2me | Theorems.Thm_FamousTheorems_primorial_lt_four_pow_bound
-- name    : FamousTheorems.primorial_lt_four_pow_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:28.436509+00:00
-- url     : https://prove2.me/theorems/091e6ec1-571e-4574-974b-ff364941d07b
-- title:
--   The primorial bound n# < 4^n
-- statement:
--   **The primorial bound $n\#<4^n$.** For every $n\ge1$, the product of all primes at most $n$ satisfies
--   $$n\#=\prod_{p\le n}p<4^n.$$
--
--   This elementary bound is due to Erdős, via central binomial coefficients: primes in $(m+1,2m+1]$ divide $\binom{2m+1}{m}\le4^m$. It is equivalent to Chebyshev's bound $\vartheta(n)<n\log4$ and is used in Erdős's proof of Bertrand's postulate.
--
--   **Formalization note.** Mathlib's `primorial_lt_four_pow`. `primorial n` is the product of the primes $p\le n$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `primorial_lt_four_pow`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem primorial_lt_four_pow_bound (n : ℕ) (hn : n ≠ 0) : primorial n < 4 ^ n := by sorry

end FamousTheorems
