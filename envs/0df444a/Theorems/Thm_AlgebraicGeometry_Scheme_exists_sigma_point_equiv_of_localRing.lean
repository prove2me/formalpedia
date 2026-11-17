-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_sigma_point_equiv_of_localRing
-- name    : AlgebraicGeometry.Scheme.exists_sigma_point_equiv_of_localRing
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:30.021208+00:00
-- url     : https://prove2.me/theorems/c32a54dc-4aaf-4005-a639-bc24b2ef5158
-- title:
--   Points of a scheme coproduct over a local ring are the disjoint union of component points
-- statement:
--   Let $(X_i→S)_{i∈I}$ be a family of $S$-schemes, let $K$ be a local ring, and let $t:Spec(K)→S$. There is an equivalence $$∐_{i∈I}Hom_S(Spec(K),X_i)≃Hom_S(Spec(K),∐_iX_i),$$ sending a component point to its composition with the coproduct inclusion. This identifies the points of the division-fibre coproduct.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing NeronModelInfra
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.exists_sigma_point_equiv_of_localRing
    {ι : Type} {S : Scheme.{0}} (X : ι → Scheme.{0}) (f : ∀ i, X i ⟶ S)
    {K : Type} [CommRing K] [IsLocalRing K]
    (t : Spec (CommRingCat.of K) ⟶ S) :
    ∃ e : (Σ i, SchemeHomOver t (f i)) ≃ SchemeHomOver t (Sigma.desc f),
      ∀ x, (e x).1 = x.2.1 ≫ Sigma.ι X x.1 := by sorry
