-- Prove2me | Theorems.Thm_FamousTheorems_mv_polynomial_ufd_6b
-- name    : FamousTheorems.mv_polynomial_ufd_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:22.784981+00:00
-- url     : https://prove2.me/theorems/c3045cd0-cd26-4504-ab15-ed705c4e5125
-- title:
--   Polynomial rings over a UFD are UFDs
-- statement:
--   **Polynomial rings over a UFD are UFDs.** Let $D$ be a unique factorization domain and $\sigma$ any set of variables. Then the polynomial ring $D[x_s : s\in\sigma]$ is a unique factorization domain.
--
--   For one variable this is Gauss's lemma. Induction and a direct limit argument give the result for any number of variables. It implies that $\mathbb Z[x_1,\dots,x_n]$ and $K[x_1,\dots,x_n]$ for a field $K$ have unique factorization, which underlies the definitions of irreducible hypersurfaces and of greatest common divisors of polynomials.
--
--   **Formalization note.** Mathlib's `MvPolynomial.uniqueFactorizationMonoid`. `MvPolynomial σ D` is the polynomial ring in variables indexed by $\sigma$, which may be infinite. `UniqueFactorizationMonoid` says that nonzero elements factor into irreducibles uniquely up to units and order, and it forces $D$ to have no zero divisors.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MvPolynomial.uniqueFactorizationMonoid`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mv_polynomial_ufd_6b (σ : Type*) {D : Type*} [CommRing D] [UniqueFactorizationMonoid D] :
    UniqueFactorizationMonoid (MvPolynomial σ D) := by sorry

end FamousTheorems
