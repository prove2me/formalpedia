-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_prime_to_characteristic
-- name    : AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-19T20:37:32.303331+00:00
-- url     : https://prove2.me/theorems/8af6d3de-ef89-434f-86ec-264b7d38d4ff
-- title:
--   Proper étale finiteness for prime coefficients invertible on the base
-- statement:
--   Let $K$ be a separably closed field, $X$ a proper $K$-scheme, and $p$ a prime. The image of $p$ in $K$ is nonzero. For every $q\geq 0$ the group
--   $$H^q_{\mathrm{et}}(X,\underline{\mathbf Z/p\mathbf Z})$$
--   is finite. The coefficient sheaf is constant on the small étale site.
-- source:
--   SGA 4, tome 3, Exposé XIV, Corollaire 1.2, https://grothendiecksga.com/read/sga4/fr/XIV-1.html.

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (p : ℕ) (hp : p.Prime)
    (hK : (p : K) ≠ 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by sorry
