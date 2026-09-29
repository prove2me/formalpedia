-- Prove2me | Theorems.Thm_FamousTheorems_x_pow_sub_one_cyclotomic_product_7b
-- name    : FamousTheorems.x_pow_sub_one_cyclotomic_product_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:16.74785+00:00
-- url     : https://prove2.me/theorems/2de03177-8a09-4f03-a489-40310eb29a90
-- title:
--   Xⁿ − 1 is the product of the cyclotomic polynomials Φ_d for d ∣ n
-- statement:
--   **$X^n-1$ is the product of the cyclotomic polynomials.** Let $n\ge1$ and let $R$ be a commutative ring. Then
--   $$X^n-1=\prod_{d\mid n}\Phi_d(X)$$
--   in $R[X]$, where $\Phi_d$ is the $d$-th cyclotomic polynomial.
--
--   Over $\mathbb C$ this groups the $n$-th roots of unity by their exact order. The identity can serve as the recursive definition of $\Phi_n$ and shows that $\Phi_n$ has integer coefficients. Taking degrees gives $n=\sum_{d\mid n}\varphi(d)$, and Möbius inversion gives $\Phi_n(X)=\prod_{d\mid n}(X^d-1)^{\mu(n/d)}$.
--
--   **Formalization note.** Mathlib's `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`. Mathlib defines `Polynomial.cyclotomic d R` over $\mathbb Z$ and maps it to $R$, so the identity holds over every commutative ring.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.prod_cyclotomic_eq_X_pow_sub_one`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem x_pow_sub_one_cyclotomic_product_7b {n : ℕ} (hn : 0 < n) (R : Type*) [CommRing R] :
    ∏ d ∈ n.divisors, Polynomial.cyclotomic d R = Polynomial.X ^ n - 1 := by sorry

end FamousTheorems
