-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isIntegral
-- name    : AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isIntegral
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T17:55:28.241169+00:00
-- url     : https://prove2.me/theorems/d717b281-b77d-4b99-a1f8-c391acea8932
-- title:
--   Proper étale finiteness with invertible prime coefficients on integral schemes
-- statement:
--   Let $K$ be a separably closed field and $X$ an integral proper scheme over $K$. For each prime $p$ whose image in $K$ is nonzero and each $q\geq 0$, the group
--   $$H^q_{\mathrm{et}}(X,\underline{\mathbf Z/p\mathbf Z})$$
--   is finite, with the constant coefficient sheaf on the small étale site.
--
--   This is the integral case of proper finiteness and supplies the input for the reduction along closed covers.
-- source:
--   SGA 4, Exposé XIV, Corollaire 1.2, restricted to integral schemes. https://fabrice.orgogozo.perso.math.cnrs.fr/SGA4/originaux/SGA4-XIVo.pdf

import Mathlib

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_isIntegral
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (p : ℕ) (hp : p.Prime)
    (hK : (p : K) ≠ 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by sorry
