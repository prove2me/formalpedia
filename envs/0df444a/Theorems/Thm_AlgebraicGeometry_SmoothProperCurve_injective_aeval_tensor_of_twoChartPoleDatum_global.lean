-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum_global
-- name    : AlgebraicGeometry.SmoothProperCurve.injective_aeval_tensor_of_twoChartPoleDatum_global
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/b2ebe22e-e6c0-5f38-bd86-80253e93f8e7
-- title:
--   Transcendence of the chart coordinate of a two-chart pole datum
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $C$ be a scheme and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, that is, a morphism $\varepsilon : \operatorname{Spec} R \to C$ together with the identity $\varepsilon$ followed by $c$ equals $\mathrm{id}_{\operatorname{Spec} R}$. Let $U, V$ be open subschemes of $C$, both affine, with $U \sqcup V = C$ as open sets, such that a point of $C$ lies in $U$ exactly when it is not in the image of the underlying map of $\varepsilon$. Let $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ be sections whose basic open sets both equal $U \cap V$, and whose restrictions to $U \cap V$ satisfy $f|_{U\cap V}\, g|_{U\cap V} = 1$. Let $K$ be a field that is an $R$-algebra, and regard $\Gamma(C,U)$ as an $R$-algebra via the map $R \to \Gamma(C,U)$ induced by $c$ (the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism followed by $c.\mathrm{appLE}\ \top\ U$). Assuming $K \otimes_R \Gamma(C,U)$ is nontrivial, the $K$-algebra map $K[X] \to K \otimes_R \Gamma(C,U)$ sending $X \mapsto 1 \otimes f$ is injective; equivalently, $1 \otimes f$ is transcendental over $K$.
--
--   This is the transcendence statement for the coordinate $f$ of a two-chart presentation of a smooth proper curve with a marked section, $U$ being the complement of the section and $f$ the function whose vanishing locus is the complementary chart's boundary; it holds over an arbitrary Noetherian base and for every field-valued point of it meeting $U$. It is used in the study of $K \otimes_R \Gamma(C,U)$ as a $K[f]$-module, namely in [`AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum_global`](thm.html#AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum_global) and in [`AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank`](thm.html#AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum_of_forall_finrank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_injective_aeval_tensor_of_twoChartPoleDatum_global.lean

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

theorem AlgebraicGeometry.SmoothProperCurve.injective_aeval_tensor_of_twoChartPoleDatum_global
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
    (K : Type u) [Field K] [Algebra R K]
    (hne : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      Nontrivial (K ⊗[R] Γ(C, U))) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Function.Injective
      (Polynomial.aeval ((1 : K) ⊗ₜ[R] f) :
        Polynomial K →ₐ[K] K ⊗[R] Γ(C, U)) := by sorry
