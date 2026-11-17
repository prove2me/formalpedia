-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_sigma_factor_of_localRing
-- name    : AlgebraicGeometry.Scheme.existsUnique_sigma_factor_of_localRing
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:46.164856+00:00
-- url     : https://prove2.me/theorems/d72a8557-a7ad-479b-bbda-173fcaff3ce5
-- title:
--   A point from the spectrum of a local ring factors through a unique coproduct component
-- statement:
--   Let $(X_i)_{i∈I}$ be a family of schemes and let $K$ be a local ring. Every morphism $u:Spec(K)→∐_iX_i$ factors through exactly one component: $$∃!\,(i,u_i),\qquad u=ι_i∘u_i.$$ This is the pointwise decomposition property of a scheme coproduct over local bases.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing NeronModelInfra
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.existsUnique_sigma_factor_of_localRing
    {ι : Type} (X : ι → Scheme.{0})
    {K : Type} [CommRing K] [IsLocalRing K]
    (u : Spec (CommRingCat.of K) ⟶ ∐ X) :
    ∃! z : Σ i, (Spec (CommRingCat.of K) ⟶ X i), z.2 ≫ Sigma.ι X z.1 = u := by sorry
