-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange
-- name    : AlgebraicGeometry.RelPicard.twoGluedSmoothCurveDegenerations_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/54f38638-1c8f-5651-945b-c00463a40cda
-- title:
--   Base change of the two-glued-curve degeneration condition
-- statement:
--   Let $R$ be a commutative ring, let $c\colon C\to\operatorname{Spec}R$ be a morphism of schemes, let $A$ be an $R$-algebra, let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec}R\to C$ with $\varepsilon$ followed by $c$ the identity), and let $U\subseteq C$ be open. Assume the following condition on $(c,\varepsilon,U)$: for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ for which the projection $C\times_R\operatorname{Spec}k\to\operatorname{Spec}k$ is not smooth, there are schemes $C_1,C_2$ with proper, smooth of relative dimension $1$, geometrically integral structure morphisms to $\operatorname{Spec}k$, closed immersions $i_1\colon C_1\to C\times_R\operatorname{Spec}k$ and $i_2\colon C_2\to C\times_R\operatorname{Spec}k$ compatible with the structure morphisms, and $n\in\mathbb{N}$ such that: every point of the fibre lies in the image of $i_1$ or of $i_2$; the scheme $C_1\times_{C\times_R\operatorname{Spec}k}C_2$ is reduced with exactly $n$ points and $n>0$; the image of the closed point of $\operatorname{Spec}k$ under the section of the fibre induced by $\varepsilon$ lies in the image of $i_1$ and not in that of $i_2$; the trace of $U$ on the fibre (the preimage of $U$ under the first projection) is the complement of the image of that intersection; the image of $i_1$ meets this trace in the connected component of the trace containing the $\varepsilon$-point, and the image of $i_2$ meets it in the remainder of the trace; and there are opens $W_1,W_2$ of the fibre whose underlying sets are the complements of the images of $i_2$ and of $i_1$ respectively, such that the inclusion of $i_1^{-1}W_1$ followed by $i_1$, and the inclusion of $i_2^{-1}W_2$ followed by $i_2$, are open immersions. The conclusion is that the same condition holds for the base-changed data: for the morphism $C\times_R\operatorname{Spec}A\to\operatorname{Spec}A$, the section obtained from $\varepsilon$ by base change, the open given by the preimage of $U$ under the projection $C\times_R\operatorname{Spec}A\to C$, and every algebraically closed field $k$ with $s'\colon\operatorname{Spec}k\to\operatorname{Spec}A$ whose fibre is not smooth.
--
--   This records that the hypothesis describing degenerations into two smooth proper geometrically integral curves crossing in finitely many reduced points, together with the position of the chosen section and the behaviour of a distinguished open, is inherited by a curve after base change of the base ring. It is used in the per-patch assembly of relative sub-Picard presheaves, where the curve over $R$ is replaced by its base change to various $R$-algebras, and relies on the comparison isomorphism between $(C\times_R\operatorname{Spec}A)\times_A\operatorname{Spec}k$ and $C\times_R\operatorname{Spec}k$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_twoGluedSmoothCurveDegenerations_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.twoGluedSmoothCurveDegenerations_baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    (hbad : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), ¬ Smooth (pullback.snd c s) →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd c s)) (i₂ : SchemeHomOver c₂ (pullback.snd c s))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback c s), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) =
          ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
            connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
              (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback c s).Opens, (W₁ : Set ↥(pullback c s)) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback c s).Opens, (W₂ : Set ↥(pullback c s)) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1))) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)), ¬ Smooth (pullback.snd (baseChange R c A) s') →
      ∃ (C₁ C₂ : Scheme.{u}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
        (_ : IsProper c₁) (_ : SmoothOfRelativeDimension 1 c₁) (_ : GeometricallyIntegral c₁)
        (_ : IsProper c₂) (_ : SmoothOfRelativeDimension 1 c₂) (_ : GeometricallyIntegral c₂)
        (i₁ : SchemeHomOver c₁ (pullback.snd (baseChange R c A) s')) (i₂ : SchemeHomOver c₂ (pullback.snd (baseChange R c A) s'))
        (_ : IsClosedImmersion i₁.1) (_ : IsClosedImmersion i₂.1) (n : ℕ),
        (∀ z : ↥(pullback (baseChange R c A) s'), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base) ∧
        IsReduced (pullback i₁.1 i₂.1) ∧ Nat.card ↥(pullback i₁.1 i₂.1) = n ∧ 0 < n ∧
        ((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.1.base \ Set.range i₂.1.base ∧
        ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
          (Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base)ᶜ ∧
        Set.range i₁.1.base ∩ ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
          connectedComponentIn ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
            (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) ∧
        Set.range i₂.1.base ∩ ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
          ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) \
            connectedComponentIn ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) : (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
              (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) ∧
        (∃ W₁ : (pullback (baseChange R c A) s').Opens, (W₁ : Set ↥(pullback (baseChange R c A) s')) = (Set.range i₂.1.base)ᶜ ∧
          IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1)) ∧
        (∃ W₂ : (pullback (baseChange R c A) s').Opens, (W₂ : Set ↥(pullback (baseChange R c A) s')) = (Set.range i₁.1.base)ᶜ ∧
          IsOpenImmersion ((i₂.1 ⁻¹ᵁ W₂).ι ≫ i₂.1)) := by sorry
