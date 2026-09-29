-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum
-- name    : AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/aac72228-6bd5-5e3d-a10a-f6754c1313b9
-- title:
--   Flatness of Γ(C,U) over R[f] for a two-chart pole datum
-- statement:
--   Let $R$ be a local Noetherian commutative ring, let $C$ be a scheme and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$ over the identity of $\operatorname{Spec} R$, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $U, V$ be open subschemes of $C$, both affine, with $U \sqcup V = C$, and suppose $U$ is exactly the complement of the image of the underlying map of $\varepsilon$: a point lies in $U$ if and only if it is not in the range of $\varepsilon$. Let $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ be sections with $U \cap V$ equal both to the basic open set of $f$ and to the basic open set of $g$, and such that the restrictions of $f$ and $g$ to $U \cap V$ have product $1$. Equip $\Gamma(C,U)$ with the $R$-algebra structure coming from $c$ (the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism for $R$ followed by the map $\Gamma(C, C) \to \Gamma(C,U)$ induced by $c$). Then the ring homomorphism $R[X] \to \Gamma(C,U)$ sending $X$ to $f$ is flat, i.e. $\Gamma(C,U)$ is a flat $R[X]$-module through $X \mapsto f$.
--
--   This is the flatness half of the statement that the affine chart $U$ of a two-chart pole datum on a proper smooth curve is a finite flat cover of the affine line via $f$; it is obtained from the fibrewise criterion of flatness over $R$, the fibres being domains in which the image of $f$ is transcendental. It is used in the proof that the relevant level sets are free, via [`AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum`](thm.html#AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_flat_aeval_of_twoChartPoleDatum.lean

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

theorem AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
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
