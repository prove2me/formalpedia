-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
-- name    : AlgebraicGeometry.geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/85f93858-a829-5c49-847b-4088a7a4c3e8
-- title:
--   Smooth plus universally bijective sections gives geometrically integral
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme and let $c : C \to \operatorname{Spec} R$ be a smooth morphism. For a commutative ring $A$ with an $R$-algebra structure write $\operatorname{Spec} A \to \operatorname{Spec} R$ for the morphism induced by $\operatorname{algebraMap} R\,A$, and form the fibre product $C \times_{\operatorname{Spec} R} \operatorname{Spec} A$; its ring of global sections carries the $A$-algebra structure obtained from the second projection, namely the ring map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$ given by the inverse of the canonical isomorphism $A \cong \Gamma(\operatorname{Spec} A, \top)$ followed by the action of the second projection on sections over the top open. The hypothesis is that for every such $A$ this structure map is bijective. The conclusion is `GeometricallyIntegral c`: the property `IsIntegral` (irreducible and reduced, hence in particular nonempty) holds for the base change of $C$ along every field-valued point of the base, i.e. $C \times_{\operatorname{Spec} R} \operatorname{Spec} K$ is an integral scheme for every field $K$ with an $R$-algebra structure.
--
--   This is the combination of the statement that a morphism with universally bijective structure map on global sections has geometrically connected base changes (as in EGA IV 4.5.13) with the fact that a smooth connected nonempty scheme over a field is integral. It supplies the `GeometricallyIntegral` hypothesis used by the relative Picard and smooth-curve chart arguments, such as [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre_of_blocks_of_injective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [Smooth c]
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) :
    GeometricallyIntegral c := by sorry
