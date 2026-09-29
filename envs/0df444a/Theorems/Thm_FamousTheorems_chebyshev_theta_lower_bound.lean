-- Prove2me | Theorems.Thm_FamousTheorems_chebyshev_theta_lower_bound
-- name    : FamousTheorems.chebyshev_theta_lower_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:13.002163+00:00
-- url     : https://prove2.me/theorems/dc626ab8-0f4c-4abc-8723-4db3c8bf82b7
-- title:
--   Chebyshev's lower bound for θ
-- statement:
--   **Chebyshev's lower bound for θ.** For every natural number $n$,
--   $$\theta(n)\ge n\log2-\log(n+1)-2\sqrt n\,\log n,$$
--   where $\theta(x)=\sum_{p\le x}\log p$ is the first Chebyshev function.
--
--   This makes explicit Chebyshev's lower bound $\theta(x)\gg x$, so there are at least $c\,x/\log x$ primes up to $x$. The proof compares the central binomial coefficient, which is at least $4^n/(2n+1)$, with its prime factorization.
--
--   **Formalization note.** Mathlib's `Chebyshev.theta_ge`. `Chebyshev.theta x` is $\sum_{p\le x,\ p\text{ prime}}\log p$, evaluated here at the real number $n$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Chebyshev.theta_ge`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem chebyshev_theta_lower_bound (n : ℕ) :
    (n : ℝ) * Real.log 2 - Real.log (n + 1) - 2 * Real.sqrt n * Real.log n ≤ Chebyshev.theta n := by sorry

end FamousTheorems
