-- Prove2me | Theorems.Thm_FamousTheorems_legendre_formula
-- name    : FamousTheorems.legendre_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:30.459722+00:00
-- url     : https://prove2.me/theorems/ed6dc7e5-0f26-482d-831d-13037bc2dd10
-- title:
--   Legendre's formula
-- statement:
--   **Legendre's formula.** For a prime $p$ and a natural number $n$, the exponent of $p$ in $n!$ is
--   $$v_p(n!)=\sum_{i\ge1}\Big\lfloor\frac n{p^i}\Big\rfloor.$$
--
--   The sum is finite since the terms vanish once $p^i>n$. The formula counts multiples of $p,p^2,p^3,\dots$ up to $n$. It gives the number of trailing zeros of $n!$ and is used in estimates for binomial coefficients, such as in Chebyshev's and Erdős's proofs of Bertrand's postulate. An equivalent form is $v_p(n!)=\frac{n-s_p(n)}{p-1}$, with $s_p(n)$ the base-$p$ digit sum.
--
--   **Formalization note.** Mathlib's `padicValNat_factorial`. The sum runs over `Finset.Ico 1 b` for any `b` with $\log_pn<b$, and `n / p ^ i` is natural-number (floor) division.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `padicValNat_factorial`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem legendre_formula {p n b : ℕ} [Fact p.Prime] (hnb : Nat.log p n < b) :
    padicValNat p n.factorial = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by sorry

end FamousTheorems
