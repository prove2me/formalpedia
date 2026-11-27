-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_etale_additive_isBaseChange_on_finite_projectiveLine_cover
-- name    : AlgebraicGeometry.Scheme.etale_additive_isBaseChange_on_finite_projectiveLine_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-27T04:31:02.710025+00:00
-- url     : https://prove2.me/theorems/6f803156-59b4-546b-8b2a-ae0417a39d9e
-- title:
--   Flat base change for additive étale cohomology on finite covers of the projective line
-- statement:
--   Over any field extension, the canonical map on degree-zero and degree-one étale cohomology of the additive structure sheaf of a finite cover of the projective line exhibits the target as scalar extension of the source.
-- source:
--   Stacks Project, Lemma 30.5.2, https://stacks.math.columbia.edu/tag/02KH, and Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Definitions.Def_AlgebraicGeometry_EtaleAdditiveCohomologyBaseChangeMap
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.etale_additive_isBaseChange_on_finite_projectiveLine_cover
    (R L E : Type u) [CommRing R] [Field L] [Field E] [Algebra L E]
    (v : Spec (.of L) ⟶ Spec (.of R)) {P T : Scheme.{u}}
    (r : P ⟶ Spec (.of L)) (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (_ : IsPullback r d v (ProjSpace.π R 1)) (j : T ⟶ Spec (.of E)) (a : T ⟶ P)
    (_ : IsPullback j a (Spec.map (CommRingCat.ofHom (algebraMap L E))) r)
    {Y : Scheme.{u}} (p : Y ⟶ P) [IsFinite p]
    (h : pullback.snd a p ≫ (p ≫ r) =
      (pullback.fst a p ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap L E))) :
    PhilipponEtaleCharacteristicComparison.IsAdditiveCohomologyBaseChangeInDegree
      (pullback.snd a p) (p ≫ r) (pullback.fst a p ≫ j) h 0 ∧
    PhilipponEtaleCharacteristicComparison.IsAdditiveCohomologyBaseChangeInDegree
      (pullback.snd a p) (p ≫ r) (pullback.fst a p ≫ j) h 1 := by sorry
