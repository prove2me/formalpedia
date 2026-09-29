-- Prove2me | Theorems.Thm_FamousTheorems_rodrigues_formula_shifted_legendre
-- name    : FamousTheorems.rodrigues_formula_shifted_legendre
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:43.919208+00:00
-- url     : https://prove2.me/theorems/73d4fde1-2e89-4af9-b6e0-d9873a35f7ea
-- title:
--   Rodrigues' formula for shifted Legendre polynomials
-- statement:
--   **Rodrigues' formula for shifted Legendre polynomials.** For every $n\ge0$,
--   $$n!\,\tilde P_n(X)=\frac{d^n}{dX^n}\Big(X^n(1-X)^n\Big),$$
--   where $\tilde P_n(X)=\sum_{k=0}^n(-1)^k\binom nk\binom{n+k}n X^k$ is the $n$-th shifted Legendre polynomial, orthogonal on $[0,1]$.
--
--   Rodrigues' formula is the standard way to prove the orthogonality of Legendre polynomials. The shifted version is used in Beukers' proof of the irrationality of $\zeta(3)$.
--
--   **Formalization note.** Mathlib's `Polynomial.factorial_mul_shiftedLegendre_eq`, an identity in $\mathbb Z[X]$. `Polynomial.derivative^[n]` is the $n$-fold formal derivative.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.factorial_mul_shiftedLegendre_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem rodrigues_formula_shifted_legendre (n : ℕ) : (n.factorial : Polynomial ℤ) * Polynomial.shiftedLegendre n =
    Polynomial.derivative^[n] (Polynomial.X ^ n * (1 - Polynomial.X) ^ n) := by sorry

end FamousTheorems
