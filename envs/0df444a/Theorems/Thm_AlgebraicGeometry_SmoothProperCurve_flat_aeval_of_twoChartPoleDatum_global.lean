-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum_global
-- name    : AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum_global
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/0ac1588a-6de7-5ce1-a8ae-5dbd61c63c1e
-- title:
--   Two-chart pole datum: Γ(C,U) is flat over R[X]
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a morphism that is proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composition with $c$ is the identity of $\operatorname{Spec} R$. Let $U, V$ be open subschemes of $C$, both affine, with $U \sqcup V = C$, and assume $U$ is exactly the complement of the image of $\varepsilon$, in the sense that a point of $C$ lies in $U$ if and only if it is not in the range of the underlying map of topological spaces of $\varepsilon$. Let $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ be sections with $U \cap V$ equal both to the basic open $D(f)$ and to the basic open $D(g)$, and such that the restrictions of $f$ and $g$ to $U \cap V$ satisfy $f g = 1$ there. Equip $\Gamma(C,U)$ with the $R$-algebra structure coming from $c$, namely the one given by the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $R$ followed by $c$'s induced map $\Gamma(\operatorname{Spec} R, \top) \to \Gamma(C,U)$. Then the ring homomorphism underlying the $R$-algebra map $R[X] \to \Gamma(C,U)$, $X \mapsto f$, is flat; equivalently, $\Gamma(C,U)$ is a flat $R[X]$-module via $X \mapsto f$.
--
--   This is the flatness half of the statement that, for a relative smooth proper curve with a section and a two-chart presentation in which the complement $U$ of the section is affine with $U \cap V = D(f)$, the coordinate $f$ exhibits $\Gamma(C,U)$ as an $R[X]$-module suitable for the study of level sets of the pole order; the base $R$ is only assumed Noetherian, not local. It feeds the construction of free bases for such level sets, as used downstream in `levelSet_free_of_twoChartPoleDatum_of_forall_finrank`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum_global.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum_global
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Flat := by sorry
