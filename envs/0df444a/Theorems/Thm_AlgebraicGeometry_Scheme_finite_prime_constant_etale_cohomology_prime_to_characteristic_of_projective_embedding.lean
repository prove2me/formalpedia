-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_prime_constant_etale_cohomology_prime_to_characteristic_of_projective_embedding
-- name    : AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_projective_embedding
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-20T19:21:13.056099+00:00
-- url     : https://prove2.me/theorems/842ec79c-f06d-45c4-9e18-63460be0c508
-- title:
--   Prime-to-characteristic étale finiteness for projective schemes
-- statement:
--   Let $K$ be a separably closed field and $X$ a closed subscheme of $\mathbf P^n_K$.
--   For a prime $p$ invertible in $K$ and every $q\geq 0$,
--   $$H^q_{\mathrm{et}}(X,\underline{\mathbf Z/p\mathbf Z})$$
--   is finite. The coefficient sheaf is constant on the small étale site. This is the projective case of proper finiteness.
-- source:
--   SGA 4, Exposé XIV, Corollaire 1.2, restricted to projective schemes. https://www.normalesup.org/~forgogozo/SGA4/14/14.pdf

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.finite_prime_constant_etale_cohomology_prime_to_characteristic_of_projective_embedding
    (K : Type u) [Field K] [IsSepClosed K] {X : Scheme.{u}} (n : ℕ)
    (e : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsClosedImmersion e]
    (p : ℕ) (hp : p.Prime) (hK : (p : K) ≠ 0) (q : ℕ) :
    Finite (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod p)))).H q) := by sorry
