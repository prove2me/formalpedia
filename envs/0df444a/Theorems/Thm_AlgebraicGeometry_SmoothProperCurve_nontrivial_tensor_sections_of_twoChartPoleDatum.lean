-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum
-- name    : AlgebraicGeometry.SmoothProperCurve.nontrivial_tensor_sections_of_twoChartPoleDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/c090e55a-8970-5609-8f48-0b039e72db1a
-- title:
--   Complement of a section has nonzero fibre algebra
-- statement:
--   Let $R$ be a local Noetherian commutative ring, and let $c : C \to \operatorname{Spec} R$ be a morphism of schemes which is proper, smooth of relative dimension $1$, and geometrically integral. Let $\varepsilon$ be a section of $c$ over the identity of $\operatorname{Spec} R$, that is, a morphism $\varepsilon_1 : \operatorname{Spec} R \to C$ whose composite with $c$ is the identity of $\operatorname{Spec} R$. Let $U, V$ be open subschemes of $C$, both affine open, with $U \sqcup V = C$ as opens, and suppose $U$ is exactly the complement of the image of $\varepsilon$ on points: a point $x$ of $C$ lies in $U$ if and only if $x$ is not in the range of the underlying map of $\varepsilon_1$. Suppose further given sections $f \in \Gamma(C, U)$ and $g \in \Gamma(C, V)$ such that $U \cap V$ equals both the basic open locus of $f$ and the basic open locus of $g$, and such that the restrictions of $f$ and $g$ to $U \cap V$ have product $1$. Finally let $K$ be a field equipped with an $R$-algebra structure. Then, with $\Gamma(C, U)$ regarded as an $R$-algebra through the ring map obtained from $c$ (the inverse of `Scheme.ΓSpecIso` followed by `c.appLE ⊤ U`), the $R$-module $K \otimes_R \Gamma(C, U)$ is nontrivial, i.e. nonzero.
--
--   This is the statement that the open complement of the section $\varepsilon$ in a smooth proper geometrically integral relative curve meets the fibre over every $R$-field $K$, expressed as non-vanishing of $K \otimes_R \Gamma(C, U)$; the hypotheses on $U$, $V$, $f$, $g$ are those of a two-chart presentation of $C$ with pole locus $\varepsilon$. It feeds into [`AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum`](thm.html#AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum), where a fibre disjoint from the chart $U$ would force the rank of the relevant level set to drop to zero, and it uses that the local ring of a smooth integral curve over a field at a rational point is a discrete valuation ring rather than a field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum.lean

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

theorem AlgebraicGeometry.SmoothProperCurve.nontrivial_tensor_sections_of_twoChartPoleDatum
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
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
