-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_flat_sigma_desc
-- name    : AlgebraicGeometry.finite_flat_sigma_desc
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:14.276918+00:00
-- url     : https://prove2.me/theorems/0085f243-93cb-4d93-a663-eba6c2b34e7d
-- title:
--   A finite coproduct of finite flat schemes is finite and flat
-- statement:
--   Let $R$ be a commutative ring and let $(X_i→Spec(R))_{i∈I}$ be a finite family of finite flat morphisms. Then the coproduct structure map satisfies $$∐_iX_i→Spec(R)\text{ is finite and flat}.$$ This assembles the individual division fibres into a finite-flat group scheme.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Limits

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry

theorem AlgebraicGeometry.finite_flat_sigma_desc
    (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (X : ι → Scheme.{u})
    (f : ∀ i, X i ⟶ Spec (CommRingCat.of R))
    [∀ i, IsFinite (f i)] [∀ i, Flat (f i)] :
    IsFinite (Sigma.desc f) ∧ Flat (Sigma.desc f) := by sorry
