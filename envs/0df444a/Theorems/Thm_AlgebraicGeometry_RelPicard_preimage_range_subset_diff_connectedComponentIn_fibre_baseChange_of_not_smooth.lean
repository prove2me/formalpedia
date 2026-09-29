-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
-- name    : AlgebraicGeometry.RelPicard.preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/74596b62-df79-5f7f-8ab7-476cbd3eaaab
-- title:
--   Transport of the off-component block condition under base change
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism, let $A$ be an $R$-algebra, let $\varepsilon$ be a section of $c$ (a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity), and let $U$ be an open of $C$. Let $z \colon Z \to C$ and $z_A \colon Z_A \to C\times_{\operatorname{Spec} R}\operatorname{Spec} A$ be morphisms of schemes such that the image of $z_A$ followed by the first projection is contained in the image of $z$ on points. Assume: for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ for which the fibre projection $\operatorname{pr}_2$ of $C\times_{\operatorname{Spec} R}\operatorname{Spec} k$ is not smooth, the preimage under $\operatorname{pr}_1$ of the image of $z$ is contained in the trace $\operatorname{pr}_1^{-1}(U)$ of $U$ on that fibre minus the connected component of that trace containing the point cut out by $\varepsilon$ (the image of the closed point of $\operatorname{Spec} k$ under the section point $\langle s\circ\varepsilon, \mathrm{id}\rangle$). Then the same holds after base change to $A$: for every algebraically closed $k$ and $s' \colon \operatorname{Spec} k \to \operatorname{Spec} A$ with non-smooth fibre projection, the $\operatorname{pr}_1$-preimage of the image of $z_A$ lies in the trace of $\operatorname{pr}_1^{-1}(U)$ minus the connected component of that trace containing the point of the base-changed section $\varepsilon_A = \langle \operatorname{Spec}(A/R)\circ\varepsilon, \mathrm{id}\rangle$.
--
--   This is a base-change transport statement for a geometric general-position condition on degenerate fibres: a locus meets every non-smooth geometric fibre only inside the trace of $U$ and away from the connected component of the section. It is used in the construction of charts with prescribed support for the relative Picard functor, in the two-sided block chart-cover theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth.lean

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

theorem AlgebraicGeometry.RelPicard.preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    {Z ZA : Scheme.{u}} (z : Z ⟶ C) (zA : ZA ⟶ pullback c (specMap R A))
    (hzA : Set.range (zA ≫ pullback.fst c (specMap R A)).base ⊆ Set.range z.base)
    (hz'ε : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' Set.range z.base ⊆
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      ¬ Smooth (pullback.snd (baseChange R c A) s') →
      (pullback.fst (baseChange R c A) s').base ⁻¹' Set.range zA.base ⊆
        ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
            (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) \
          connectedComponentIn
            ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
                (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
            (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) := by sorry
