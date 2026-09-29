-- Prove2me | Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
-- name    : AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/c79104af-d364-5cc7-825f-68910015a6df
-- title:
--   Rigidity: geometric points over ̄ K determine morphisms
-- statement:
--   Let $R$ be a commutative integral domain, let $K$ be a field that is a fraction field of $R$ (via its $R$-algebra structure), and let $\overline K$ be a field that is an algebraic closure of $K$, equipped with an $R$-algebra structure compatible with those of $K$ over $R$ and of $\overline K$ over $K$. Let $Y$ and $X$ be schemes with structure morphisms $g_Y\colon Y\to\operatorname{Spec} R$ and $g_X\colon X\to\operatorname{Spec} R$, where $g_Y$ is flat and locally of finite type, $Y$ is reduced, and $g_X$ is separated. Let $\varphi$ and $\psi$ be two morphisms over $\operatorname{Spec} R$, i.e. elements of `SchemeHomOver gY gX`: pairs consisting of a morphism $Y\to X$ together with a proof that its composite with $g_X$ equals $g_Y$. Assume that for every $\overline K$-valued geometric point of $Y$ over $R$ — that is, every pair consisting of a morphism $x\colon\operatorname{Spec}\overline K\to Y$ together with a proof that $x$ followed by $g_Y$ equals the morphism $\operatorname{Spec}\overline K\to\operatorname{Spec} R$ induced by $R\to\overline K$ — one has $x$ followed by $\varphi$ equal to $x$ followed by $\psi$. Then $\varphi=\psi$ as elements of `SchemeHomOver gY gX`, in particular the two morphisms $Y\to X$ coincide.
--
--   This is a rigidity (schematic density) statement: on a reduced scheme flat and locally of finite type over a domain, an $\operatorname{Spec} R$-morphism into a separated scheme is determined by its values on geometric points with values in an algebraic closure of the fraction field. It is used throughout the Néron-model infrastructure of the project, for instance to reduce identities of morphisms of group schemes to identities on $\overline K$-points, and it is specialised further to the case of an algebraically closed base and to a criterion for closed immersions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar] [IsScalarTower R K Kbar]
    {Y X : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of R)} {gX : X ⟶ Spec (CommRingCat.of R)}
    [Flat gY] [LocallyOfFiniteType gY] [IsReduced Y] [IsSeparated gX]
    (φ ψ : SchemeHomOver gY gX)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gY, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by sorry
