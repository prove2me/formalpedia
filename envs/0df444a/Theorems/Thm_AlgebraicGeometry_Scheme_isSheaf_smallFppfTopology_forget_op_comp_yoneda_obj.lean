-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
-- name    : AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/f3da3b7c-5242-520d-813f-3bd36d31eb28
-- title:
--   Functor of points is a small fppf sheaf
-- statement:
--   Let $S$ be a scheme (in universe $u$) and let $X$ be an object of the category `Over S`, that is, a scheme together with a morphism to $S$; no further hypothesis is imposed on $X \to S$. The small fppf site of $S$ is the category $S$`.Fppf` $=$ `MorphismProperty.Over fppfProperty ⊤ S`, whose objects are the $S$-schemes $U \to S$ whose structure morphism is flat and locally of finite presentation (`fppfProperty` being the infimum of `@Flat` and `@LocallyOfFinitePresentation`) and whose morphisms are all morphisms of $S$-schemes between such objects, equipped with the Grothendieck topology `smallFppfTopology S`, namely Mathlib's small Grothendieck topology on this category attached to the morphism property `fppfProperty`. The presheaf of types under consideration is obtained by composing the opposite of the forgetful functor `Scheme.Fppf.forget S : S.Fppf ⥤ Over S` with the representable presheaf `yoneda.obj X` on `Over S`; concretely it sends an object $U \to S$ of the small fppf site to the set $\operatorname{Hom}_S(U, X)$ of $S$-morphisms $U \to X$, with the evident restriction maps. The assertion is that this presheaf satisfies the sheaf condition for `smallFppfTopology S`.
--
--   This is faithfully flat descent for morphisms of schemes, phrased as the statement that the functor of points of an arbitrary $S$-scheme is a sheaf on the small fppf site of $S$ (equivalently, that the small fppf topology is subcanonical on representables coming from `Over S`). It is used in the construction of relative group laws, where it supplies the sheaf whose sections recover the $S$-points, in [`GoodReductionJacobian.RelativeGroupLaw.exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

theorem AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
    (S : Scheme.{u}) (X : Over S) :
    Presheaf.IsSheaf (smallFppfTopology S) ((Scheme.Fppf.forget S).op ⋙ yoneda.obj X) := by sorry
