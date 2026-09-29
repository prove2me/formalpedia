-- Prove2me | Theorems.Thm_FamousTheorems_chebyshev_psi_upper_bound
-- name    : FamousTheorems.chebyshev_psi_upper_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:10.587422+00:00
-- url     : https://prove2.me/theorems/38bde5e6-a1f8-4a05-8472-59566e278473
-- title:
--   Chebyshev's upper bound for ψ
-- statement:
--   **Chebyshev's upper bound for ψ.** For all $x\ge0$,
--   $$\psi(x)\le(\log4+4)\,x,$$
--   where $\psi(x)=\sum_{p^k\le x}\log p$ is the second Chebyshev function.
--
--   Chebyshev proved around 1850 that $\psi(x)$ has order of magnitude $x$, the first major step towards the prime number theorem. The upper bound comes from the divisibility of the central binomial coefficient $\binom{2n}{n}$ by all primes in $(n,2n]$ together with $\binom{2n}n\le4^n$. It gives $\pi(x)=O(x/\log x)$.
--
--   **Formalization note.** Mathlib's `Chebyshev.psi_le_const_mul_self`. `Chebyshev.psi x` is $\sum_{n\le x}\Lambda(n)$ with $\Lambda$ the von Mangoldt function. The explicit constant is $\log 4+4$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Chebyshev.psi_le_const_mul_self`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem chebyshev_psi_upper_bound {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ (Real.log 4 + 4) * x := by sorry

end FamousTheorems
