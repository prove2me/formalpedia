-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/ada673c3-4380-52f3-b68f-17f8b896eb49
-- title:
--   Base change of a Laurent chart along R → A
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $\mathcal V$ a two-affine-open cover of $X$ (affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine), $c\colon X\to\operatorname{Spec}R$ a morphism, and $A$ a commutative $R$-algebra. Write $\mathcal U=\mathcal V.\mathrm{cover}\ c$ for the associated two-chart Čech cover, with $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\cap U_1)$ as $R$-algebras via $c$ and $\rho_0,\rho_1$ the restriction maps, and let $\Lambda$ be a Laurent chart on $\mathcal U$, that is a ring homomorphism $\Lambda.\mathrm{expand}\colon A_{01}\to R(\!(t)\!)$ carrying $\mathrm{algebraMap}\,R\,A_{01}(r)$ to the constant series $C(r)$. Let $\mathcal V_A$ be the cover of $X\times_{\operatorname{Spec}R}\operatorname{Spec}A$ obtained by pulling back $U_0,U_1$ along the first projection, regarded over $\operatorname{Spec}A$ by the second projection. Then there is a Laurent chart $\Lambda_A$ on the resulting cover such that for every $y\in A_{01}$ one has $\Lambda_A.\mathrm{expand}$ of the image of $y$ under the restriction map `map01` of the base-change morphism over $\mathrm{algebraMap}\,R\,A$ equal to the coefficientwise image of $\Lambda.\mathrm{expand}(y)$ under $\mathrm{algebraMap}\,R\,A$; $\Lambda_A$ is the unique chart with this property; and if every element of $A_0$ (resp. $A_1$) has expansion in the image of $R[\![t]\!]$, the same holds for the base-changed cover, while if some element of $A_0$ (resp. $A_1$) has expansion $t$, the same holds after base change.
--
--   This supplies, for an arbitrary $R$-algebra $A$, the "corresponding chart" datum on the base-changed two-chart cover that the base-change theorems for residues and for the integral Serre pairing take as a hypothesis; it rests on the identification of the structure-sheaf sections of the pullback with $A\otimes_R(-)$ for affine base change. It is used in the treatment of residues vanishing on coboundaries and in the sectional-curve statements about completions, parameters and bijectivity of the integral Serre pairing, in particular for passage to the generic and special fibres of a curve over a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_baseChange
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (Λ : (𝒱.cover c).LaurentChart) :
    ∃ ΛA : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
      (∀ y : (𝒱.cover c).A01,
        ΛA.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) ∧
      (∀ Λ' : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
        (∀ y : (𝒱.cover c).A01,
          Λ'.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) →
        Λ' = ΛA) ∧
      (Λ.IsRegular (𝒱.cover c).ρ0 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.IsRegular (𝒱.cover c).ρ1 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) ∧
      (Λ.HasParameter (𝒱.cover c).ρ0 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.HasParameter (𝒱.cover c).ρ1 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) := by sorry
