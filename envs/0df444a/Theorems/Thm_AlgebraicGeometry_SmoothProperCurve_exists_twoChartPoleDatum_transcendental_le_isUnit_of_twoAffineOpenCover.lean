-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/0ac68895-6a2e-5e34-900b-8bfbd35422e5
-- title:
--   Two-chart pole datum of large unit order, cover-input form
-- statement:
--   Let $R$ be a commutative Noetherian local ring (in a fixed universe), let $C$ be a scheme and $c \colon C \to \operatorname{Spec} R$ a proper morphism that is smooth of relative dimension $1$ and geometrically integral, let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity), let $\mathcal V$ be a presentation of $C$ as a union of two affine opens with affine intersection, and let $m_0$ be a natural number. Then there exist opens $U, V \subseteq C$ with $U \sqcup V = \top$, with $U$ consisting exactly of the points outside the image of $\varepsilon$, sections $f \in \Gamma(C, U)$ and $g \in \Gamma(C, V)$ with $U \cap V = C_f = C_g$ (the basic opens of $f$ and of $g$) and with the restrictions of $f$ and $g$ to $U \cap V$ multiplying to $1$, and a natural number $m$ such that: $m_0 \le m$; $m$ is a unit in $R$; with respect to the $R$-algebra structure on $\Gamma(C, V)$ induced by $c$, the quotient $\Gamma(C,V)/(g)$ is a free $R$-module of rank $m$; and for every field $K$ that is an $R$-algebra, the images of $f$ and of $g$ under restriction along the first projection of the base change $C \times_{\operatorname{Spec} R} \operatorname{Spec} K$ (over the preimages of $U$ and of $V$, carrying the $K$-algebra structures induced by the second projection) are transcendental over $K$.
--
--   This is the existence of a rational function on a relative smooth proper curve with a single pole, of prescribed large order $m$ invertible in the base, concentrated along a given section, packaged as a two-chart datum: a trivialising pair $U = C \setminus \varepsilon$, $V \ni \varepsilon$ together with mutually inverse units $f, g$ on the overlap and the freeness of $\Gamma(C,V)/(g)$ of rank $m$. It is the form consumed in the construction of finite-map data for integral models of curves, where the two-affine cover $\mathcal V$ supplied as input is the one coming from the model at hand.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_twoChartPoleDatum_transcendental_le_isUnit_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover) (m₀ : ℕ) :
    ∃ (U V : C.Opens) (_ : U ⊔ V = ⊤)
      (_ : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
      (f : Γ(C, U)) (g : Γ(C, V))
      (_ : U ⊓ V = C.basicOpen f) (_ : U ⊓ V = C.basicOpen g)
      (_ : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
        (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
      (m : ℕ),
      m₀ ≤ m ∧ IsUnit (m : R) ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
        Module.Free R (Γ(C, V) ⧸ Ideal.span {g}) ∧ Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m) ∧
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
