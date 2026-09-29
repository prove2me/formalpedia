-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_range_subset_connectedComponentIn_fibre_baseChange
-- name    : AlgebraicGeometry.RelPicard.preimage_range_subset_connectedComponentIn_fibre_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/96be0db8-67dd-5f1a-acb6-be0e608e4d8e
-- title:
--   Base change stability of fibrewise containment in the section component
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes, $A$ an $R$-algebra, and let $\varepsilon$ be a section of $c$ over the identity of $\operatorname{Spec}R$, that is, a morphism $\varepsilon_1\colon\operatorname{Spec}R\to C$ with $\varepsilon_1$ followed by $c$ equal to the identity. Let $U\subseteq C$ be an open subscheme, and let $z\colon Z\to C$ and $z_A\colon Z_A\to C\times_{\operatorname{Spec}R}\operatorname{Spec}A$ be morphisms of schemes, where the fibre product is taken along $\operatorname{Spec}$ of the structure map $R\to A$. Assume, on underlying topological spaces, that the image of $z_A$ followed by the first projection to $C$ is contained in the image of $z$; and assume that for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ the preimage under the first projection $C\times_{\operatorname{Spec}R}\operatorname{Spec}k\to C$ of the image of $z$ is contained in the connected component, within the open set obtained as the preimage of $U$, of the point obtained by evaluating at the closed point of $\operatorname{Spec}k$ the canonical lift of $(s$ followed by $\varepsilon_1,\ \mathrm{id})$ into the fibre. Then the same holds after base change to $A$: for every algebraically closed field $k$ and every $s'\colon\operatorname{Spec}k\to\operatorname{Spec}A$, the preimage under the first projection of the image of $z_A$ lies in the connected component, inside the preimage of the preimage of $U$ in $C\times_{\operatorname{Spec}R}\operatorname{Spec}A$, of the closed-point value of the section of the base-changed morphism induced by $\varepsilon$.
--
--   This is a transport statement for the fibrewise condition that the image of an auxiliary morphism (a block) lies on the connected component of the marked section inside a prescribed open subscheme: the condition for the family $c$ over $\operatorname{Spec}R$ implies the corresponding condition for the base-changed family over $\operatorname{Spec}A$. It is used in the construction of charts in the relative Picard package, namely by [`AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective`](thm.html#AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_and_support_subset_fibre_of_twoSidedBlocks_of_injective). No hypotheses of properness, flatness or smoothness on $c$ enter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_preimage_range_subset_connectedComponentIn_fibre_baseChange.lean

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

theorem AlgebraicGeometry.RelPicard.preimage_range_subset_connectedComponentIn_fibre_baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    {Z ZA : Scheme.{u}} (z : Z ⟶ C) (zA : ZA ⟶ pullback c (specMap R A))
    (hzA : Set.range (zA ≫ pullback.fst c (specMap R A)).base ⊆ Set.range z.base)
    (hzε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      (pullback.fst c s).base ⁻¹' Set.range z.base ⊆
        connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
          (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      (pullback.fst (baseChange R c A) s').base ⁻¹' Set.range zA.base ⊆
        connectedComponentIn
          ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
              (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
          (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) := by sorry
