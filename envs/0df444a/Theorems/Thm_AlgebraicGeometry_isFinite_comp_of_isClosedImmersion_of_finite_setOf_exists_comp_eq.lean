-- Prove2me | Theorems.Thm_AlgebraicGeometry_isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq
-- name    : AlgebraicGeometry.isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/2a5a4101-b53b-52d7-b8a5-6d8bf35fc89e
-- title:
--   Finitely many k-points forces finiteness over k
-- statement:
--   Let $k$ be an algebraically closed field, and let $A$ and $K$ be schemes (in the bottom universe). Let $f : A \to \operatorname{Spec} k$ be a morphism that is quasi-compact and locally of finite type, and let $\iota : K \to A$ be a closed immersion. Consider the set of $k$-sections of $f$, that is, of pairs consisting of a morphism $\varphi : \operatorname{Spec} k \to A$ together with the condition that $\varphi$ followed by $f$ is the identity of $\operatorname{Spec} k$ (this is the type `SchemeHomOver` of morphisms over $\operatorname{Spec} k$ from the identity to $f$), and inside it the subset of those $\varphi$ which factor through $\iota$, i.e. for which there exists $y : \operatorname{Spec} k \to K$ with $y$ followed by $\iota$ equal to $\varphi$. The hypothesis is that this subset is finite. The conclusion is that the composite $\iota$ followed by $f$, from $K$ to $\operatorname{Spec} k$, is a finite morphism.
--
--   This is the standard fact that a closed subscheme of a scheme of finite type over an algebraically closed field having only finitely many $k$-points is finite over $k$; here the $k$-points of $K$ are counted as sections of $f$ factoring through the closed immersion. It is used in the study of Riemann forms, in the proof that the Euler characteristic of an invertible sheaf is non-zero and divisible by a suitable power, where the relevant $K$ is the stabiliser subscheme presented as a closed subscheme of $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_RiemannForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq
    (k : Type) [Field k] [IsAlgClosed k] {A K : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [LocallyOfFiniteType f]
    (ι : K ⟶ A) [IsClosedImmersion ι]
    (hfin : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f | ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1}.Finite) :
    IsFinite (ι ≫ f) := by sorry
