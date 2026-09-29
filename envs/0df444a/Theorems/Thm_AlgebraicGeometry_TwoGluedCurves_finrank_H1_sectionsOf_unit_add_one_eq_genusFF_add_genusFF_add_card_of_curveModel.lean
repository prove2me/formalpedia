-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_finrank_H1_sectionsOf_unit_add_one_eq_genusFF_add_genusFF_add_card_of_curveModel
-- name    : AlgebraicGeometry.TwoGluedCurves.finrank_H1_sectionsOf_unit_add_one_eq_genusFF_add_genusFF_add_card_of_curveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/c9e095be-ee8c-5bae-b57b-bfb33a42e272
-- title:
--   Genus of two smooth curves glued at s points
-- statement:
--   Let $k$ be an algebraically closed field, and let $x : X \to \operatorname{Spec} k$ be a proper morphism with $X$ reduced. Let $c_1 : C_1 \to \operatorname{Spec} k$ and $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension one and geometrically integral, and let $i_1, i_2$ be morphisms $C_1 \to X$, $C_2 \to X$ over $k$ (i.e. pairs consisting of a scheme morphism together with a proof that composing it with $x$ gives $c_1$, resp. $c_2$) which are closed immersions. Assume every point of $X$ lies in the image of $i_1$ or of $i_2$, that the fibre product $C_1 \times_X C_2$ is reduced, and that its underlying point set has cardinality $s$ with $s > 0$. Let $F_1, F_2$ be fields over $k$, each equipped with a `CurveModel` over $k$: an integral scheme, proper and smooth of relative dimension one over $k$, together with a ring isomorphism of $F_i$ with its function field extending $k$, a bijection from closed points to places of $F_i/k$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open; assume the model schemes are isomorphic to $C_1$, resp. $C_2$, compatibly with the structure morphisms. Finally let $\mathcal W$ be a cover of $X$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = X$ and $U_0 \cap U_1$ affine. Then the $k$-dimension of the two-chart Čech $H^1$ of the structure sheaf of $X$ with respect to $\mathcal W$, namely $\Gamma(U_0 \cap U_1)$ modulo the image of the difference-of-restrictions map from $\Gamma(U_0) \oplus \Gamma(U_1)$, satisfies $$\dim_k H^1 + 1 = g(F_1) + g(F_2) + s,$$ where $g(F_i) = \dim_k \big(\text{repartitions of } F_i/k \big/ (\text{repartitions with no poles} + \text{principal repartitions})\big)$.
--
--   This is the genus formula for a curve obtained by glueing two smooth proper curves transversally at $s$ points: the arithmetic genus is $g_1 + g_2 + s - 1$, stated additively over $\mathbb N$ and with the genera read off from the function fields via repartitions. It is used in the computation of the genus of the modular curve $X_1(p)$ through its two-chart model and the special fibre count of supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_finrank_H1_sectionsOf_unit_add_one_eq_genusFF_add_genusFF_add_card_of_curveModel.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.TwoGluedCurves.finrank_H1_sectionsOf_unit_add_one_eq_genusFF_add_genusFF_add_card_of_curveModel
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)

    (F₁ F₂ : Type u) [Field F₁] [Algebra k F₁] [Field F₂] [Algebra k F₂]
    (Mdl₁ : AlgebraicCurve.CurveModel k F₁) (e₁ : Mdl₁.C ≅ C₁) (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k F₂) (e₂ : Mdl₂.C ≅ C₂) (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)
    (𝒲 : X.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H1 + 1 =
      AlgebraicCurve.genusFF k F₁ + AlgebraicCurve.genusFF k F₂ + s := by sorry
