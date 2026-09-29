-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/e3ed29e3-2b33-5f96-9f82-be79e8c21850
-- title:
--   Čech h¹ of mathcal O_C equals the genus of the function field
-- statement:
--   Let $k$ be an algebraically closed field and let $c : C \to \operatorname{Spec} k$ be a morphism of schemes that is proper, smooth of relative dimension $1$, and geometrically integral. Let $F$ be a field equipped with a $k$-algebra structure and let $\mathrm{Mdl}$ be a `CurveModel` for $F$ over $k$: a scheme $\mathrm{Mdl}.C$ with a proper, smooth-of-relative-dimension-one morphism $\mathrm{Mdl}.\mathrm{toBase}$ to $\operatorname{Spec} k$ and integral underlying scheme, a ring isomorphism of $F$ with the function field of $\mathrm{Mdl}.C$ compatible with the structure map from $k$, a bijection from the closed points of $\mathrm{Mdl}.C$ onto the places of $F/K$ matching each stalk with the corresponding valuation subring, and the property that every finite set of points lies in an affine open. Assume $e : \mathrm{Mdl}.C \cong C$ is an isomorphism of schemes with $e$ followed by $c$ equal to $\mathrm{Mdl}.\mathrm{toBase}$. Finally let $\mathcal W$ be a cover of $C$ by two opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and with $U_0$, $U_1$ and $U_0 \sqcap U_1$ all affine. Then the $k$-dimension of the first Čech cohomology of the structure sheaf for this two-chart cover — that is, of $\Gamma(\mathcal O_C, U_0 \sqcap U_1)$ modulo the image of the map $(s_0,s_1) \mapsto s_1|_{U_0 \cap U_1} - s_0|_{U_0 \cap U_1}$ from $\Gamma(\mathcal O_C,U_0) \times \Gamma(\mathcal O_C,U_1)$ — equals $\mathrm{genusFF}\ k\ F$, the $k$-dimension of the quotient of the algebra of repartitions of $F/k$ by the sum of the repartitions bounded by the zero divisor and the principal repartitions.
--
--   This is the comparison between the Čech cohomology of the structure sheaf of a smooth proper curve and the repartition (adelic) cohomology of its function field, identifying the geometric $h^1(\mathcal O_C)$ with the genus of $F/k$ defined via repartitions. It is used in the computation of genera of glued curves and, downstream, in the genus formula for the modular curves occurring in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_genusFF_of_curveModel
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (F : Type u) [Field F] [Algebra k F] (Mdl : AlgebraicCurve.CurveModel k F) (e : Mdl.C ≅ C)
    (he : e.hom ≫ c = Mdl.toBase)
    (𝒲 : C.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H1 = AlgebraicCurve.genusFF k F := by sorry
