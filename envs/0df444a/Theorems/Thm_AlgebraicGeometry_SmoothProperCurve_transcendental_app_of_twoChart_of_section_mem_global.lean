-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_transcendental_app_of_twoChart_of_section_mem_global
-- name    : AlgebraicGeometry.SmoothProperCurve.transcendental_app_of_twoChart_of_section_mem_global
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/c725a804-d71d-59df-abe5-abf09da8e257
-- title:
--   Fibrewise transcendence of the two-chart coordinates f, g
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a morphism that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is, a morphism $\varepsilon : \operatorname{Spec} R \to C$ together with the identity $\varepsilon \text{ followed by } c = \mathrm{id}$. Let $U, V$ be opens of $C$ with $U \sqcup V = C$, such that a point of $C$ lies in $U$ exactly when it is not in the image of the underlying map of $\varepsilon$, and every point in that image lies in $V$. Let $f \in \Gamma(C, U)$ and $g \in \Gamma(C, V)$ satisfy $U \cap V = C_f = C_g$ (the basic opens of $f$ and of $g$), and let the restrictions of $f$ and $g$ to $U \cap V$ have product $1$. The conclusion is the conjunction of two assertions, one for $f$ and one for $g$: for every field $K$ (in the same universe) with an $R$-algebra structure, form the pullback of $c$ along $\operatorname{Spec}$ of the structure map $R \to K$, with projections $p_1$ to $C$ and $p_2$ to $\operatorname{Spec} K$; then $\Gamma$ of the pullback over $p_1^{-1}U$, regarded as a $K$-algebra through $p_2$ (via the composite of the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism for $K$ with the appropriate component of $p_2$), contains the image of $f$ under the component of $p_1$ at $U$ as a transcendental element over $K$, and likewise the image of $g$ under the component of $p_1$ at $V$ is transcendental over $K$ in $\Gamma$ of the pullback over $p_1^{-1}V$.
--
--   This is the transcendence statement for the two coordinate functions of a two-chart datum on a smooth proper geometrically integral relative curve with a section, asserted fibrewise over every field extending the base, with no hypothesis on the order of the pole along the section. It is used in the construction of pole data with prescribed finite ranks, namely by [`AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_forall_finrank_of_section_invModule`](thm.html#AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_forall_finrank_of_section_invModule), and its proof appeals to the fact that the stalk at a section of a smooth relative curve of dimension one over a field is a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_transcendental_app_of_twoChart_of_section_mem_global.lean

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

theorem AlgebraicGeometry.SmoothProperCurve.transcendental_app_of_twoChart_of_section_mem_global
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) := by sorry
