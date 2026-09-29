-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_eq_of_forall_sub_algebraMap_mem_nonunits_of_twoChartIntegralModel
-- name    : AlgebraicCurve.CurveModel.pointEquivPlace_eq_of_forall_sub_algebraMap_mem_nonunits_of_twoChartIntegralModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/85906abe-901c-522b-a90c-1ca24e965f62
-- title:
--   Places determined by centres on a two-chart model
-- statement:
--   Let $R$ be a commutative ring, $F_0$ a field with an $R$-algebra structure and $j \in F_0$ nonzero; let $K$ be an algebraically closed field and $F$ a field extension of $K$. Let $N$ be a `CurveModel` for $F/K$, so that $N.C$ is an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec} K$ via `N.toBase`, with $F$ identified with the function field of $N.C$ compatibly with $K$ and with a bijection `N.placeOfPoint` from closed points of $N.C$ onto places of $F/K$ (valuation subrings of $F$ containing $K$, proper, and principal ideal rings) whose valuation subring is the image of the local ring at the point; write `N.pointEquivPlace` for the induced bijection from the $K$-points of $N.C$, i.e. the morphisms $q \colon \operatorname{Spec} K \to N.C$ splitting `N.toBase`, onto places. Let $h \colon N.C \to \mathfrak{X}$ be a morphism to the two-chart integral model `TwoChartIntegralModel R F₀ j`, the pushout glueing $\operatorname{Spec}$ of the algebra of elements of $F_0$ integral over $R[j]$ to $\operatorname{Spec}$ of the algebra of elements integral over $R[j^{-1}]$, and assume $h$ is injective on $K$-points. Let $\pi_F$ and $\pi_I$ be ring homomorphisms from the finite and the infinite chart algebra to $F$ with $\pi_I(j^{-1}) \cdot \pi_F(j) = 1$, and assume the centring laws: whenever a $K$-point $y$ of $N.C$ satisfies $h \circ y = \iota_{\mathrm{fin}} \circ \operatorname{Spec}(\beta)$ for a ring homomorphism $\beta$ from the finite chart algebra to $K$, then $\pi_F(b) - \beta(b)$ lies in the nonunits of the valuation subring of `N.pointEquivPlace y` for every chart element $b$, and likewise for the infinite chart with $\pi_I$ and $\iota_{\infty}$. The conclusion is the conjunction of two converse statements: for every place $w$ of $F/K$ and every ring homomorphism $\beta$ from the finite chart algebra to $K$ with $\pi_F(b) - \beta(b)$ a nonunit of $w$ for all $b$, every $K$-point $y$ with $h \circ y = \iota_{\mathrm{fin}} \circ \operatorname{Spec}(\beta)$ satisfies `N.pointEquivPlace y = w`; and the same with the infinite chart algebra, $\pi_I$ and $\iota_{\infty}$ in place of the finite data.
--
--   This is the valuative bookkeeping step asserting that a place of the function field is recognised by its centre on the two-chart model: a chart-centring congruence for a given place pins down which $K$-point of the smooth proper model carries it. It is used in the identification of points with places for fibre models of the two-chart model attached to $X_1(M)$ and the $j$-line, where it feeds the comparison of divisor classes on $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_pointEquivPlace_eq_of_forall_sub_algebraMap_mem_nonunits_of_twoChartIntegralModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.pointEquivPlace_eq_of_forall_sub_algebraMap_mem_nonunits_of_twoChartIntegralModel
    {R F₀ : Type u} [CommRing R] [Field F₀] [Algebra R F₀] (j : F₀) [Fact (j ≠ 0)]
    {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    (N : AlgebraicCurve.CurveModel K F) (h : N.C ⟶ AlgebraicCurve.TwoChartIntegralModel R F₀ j)
    (hinj : ∀ y y' : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}, y.1 ≫ h = y'.1 ≫ h → y = y')
    (πF : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F₀ j) →+* F) (πI : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F₀ j) →+* F)
    (hπj : πI (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf R F₀ j) * πF (AlgebraicCurve.TwoChartIntegralModel.jChartFin R F₀ j) = 1)
    (hcenF : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F₀ j) →+* K),
      y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin R F₀ j →
      ∀ b, πF b - algebraMap K F (β b) ∈ (N.pointEquivPlace y).toValuationSubring.nonunits)
    (hcenI : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F₀ j) →+* K),
      y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf R F₀ j →
      ∀ b, πI b - algebraMap K F (β b) ∈ (N.pointEquivPlace y).toValuationSubring.nonunits) :
    (∀ (w : AlgebraicCurve.Place K F) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F₀ j) →+* K),
        (∀ b, πF b - algebraMap K F (β b) ∈ w.toValuationSubring.nonunits) →
        ∀ y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}, y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin R F₀ j → N.pointEquivPlace y = w) ∧
    (∀ (w : AlgebraicCurve.Place K F) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F₀ j) →+* K),
        (∀ b, πI b - algebraMap K F (β b) ∈ w.toValuationSubring.nonunits) →
        ∀ y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _}, y.1 ≫ h = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf R F₀ j → N.pointEquivPlace y = w) := by sorry
