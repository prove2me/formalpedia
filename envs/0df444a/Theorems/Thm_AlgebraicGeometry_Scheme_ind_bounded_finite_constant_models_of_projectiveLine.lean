-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ind_bounded_finite_constant_models_of_projectiveLine
-- name    : AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models_of_projectiveLine
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-26T06:03:11.659711+00:00
-- url     : https://prove2.me/theorems/18a50393-e49a-49e8-86d6-4d640d8e0435
-- title:
--   Bounded finite constant models for étale sheaves on the projective line
-- statement:
--   On the base change of a projective-line projection to a field, every abelian étale sheaf annihilated by a nonzero integer is a filtered colimit of sheaves that embed in the direct image of a finite constant sheaf under a finite morphism of finite presentation. The same integer annihilates each finite coefficient group.
-- source:
--   Stacks Project, Lemma 59.74.3, https://stacks.math.columbia.edu/tag/09Z6.

import Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models_of_projectiveLine
    (R K : Type u) [CommRing R] [Field K] (v : Spec (.of K) ⟶ Spec (.of R))
    {P : Scheme.{u}} (r : P ⟶ Spec (.of K))
    (d : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) R))
    (hP : IsPullback r d v (ProjSpace.π R 1)) (N : ℕ) (hN : N ≠ 0)
    (F : Sheaf P.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0) :
    ObjectProperty.ind.{u} (PhilipponEtaleBoundedFiniteModelReduction.boundedFiniteModel P N) F := by sorry
