-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isReduced
-- name    : AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isReduced
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T16:17:25.599454+00:00
-- url     : https://prove2.me/theorems/8fd97888-b6c8-432d-8df0-f821c3026c49
-- title:
--   Proper étale finiteness with invertible prime coefficients on reduced schemes
-- statement:
--   Let $K$ be a separably closed field and let $X$ be a reduced proper scheme over $K$. Let $p$ be a prime whose image in $K$ is nonzero. For every $q\geq 0$ the group
--   $$H^q_{\mathrm{et}}(X,\underline{\mathbf Z/p\mathbf Z})$$
--   is finite, where the coefficient sheaf is constant on the small étale site.
-- source:
--   SGA 4, Exposé XIV, Corollary 1.2, restricted to reduced schemes. https://fabrice.orgogozo.perso.math.cnrs.fr/SGA4/originaux/SGA4-XIVo.pdf

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isReduced
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}} [IsReduced X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (p : ℕ) (hp : p.Prime)
    (hK : (p : K) ≠ 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by sorry
