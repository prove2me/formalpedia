-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum_global
-- name    : AlgebraicGeometry.SmoothProperCurve.nontrivial_tensor_sections_of_twoChartPoleDatum_global
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/5725d4f2-65fc-5e2e-85fc-67682a7a2d33
-- title:
--   Nontriviality of K ⊗_R Γ(C,U) for a two-chart pole datum
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $C$ be a scheme and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, that is, a morphism $\varepsilon : \operatorname{Spec} R \to C$ with $\varepsilon$ followed by $c$ equal to the identity of $\operatorname{Spec} R$. Let $U, V$ be open subschemes of $C$, both affine, with $U \sqcup V = \top$, and assume $U$ is exactly the complement of the image of the underlying map of $\varepsilon$: a point $x$ of $C$ lies in $U$ if and only if $x$ is not in the range of $\varepsilon$ on points. Let $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ be sections such that $U \sqcap V$ equals both the basic open set of $f$ and the basic open set of $g$, and such that the restrictions of $f$ and of $g$ to $U \sqcap V$ have product $1$. Let $K$ be a field equipped with an $R$-algebra structure. Then, for the $R$-algebra structure on $\Gamma(C,U)$ obtained from the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism of $R$ followed by $c.\mathrm{appLE}\ \top\ U$, the ring $K \otimes_R \Gamma(C,U)$ is nontrivial, i.e. nonzero.
--
--   This records that the complement of a section of a smooth proper relative curve with geometrically integral fibres survives base change to any field over the base: $K \otimes_R \Gamma(C,U)$ is the coordinate ring of $U_K = C_K \setminus \varepsilon$, and it is nonzero because the fibre is an integral curve while $\varepsilon$ cuts out a point whose local ring is a discrete valuation ring, not the whole fibre. It is used in the computation of the rank of the level sets of the chart coordinate on every fibre, via [`AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank`](thm.html#AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank), where a fibre missed by the chart would otherwise contribute rank $0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum_global.lean

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

theorem AlgebraicGeometry.SmoothProperCurve.nontrivial_tensor_sections_of_twoChartPoleDatum_global
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Nontrivial (K ⊗[R] Γ(C, U)) := by sorry
