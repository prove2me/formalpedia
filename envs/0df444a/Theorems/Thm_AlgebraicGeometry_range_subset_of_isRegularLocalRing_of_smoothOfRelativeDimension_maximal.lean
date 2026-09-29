-- Prove2me | Theorems.Thm_AlgebraicGeometry_range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal
-- name    : AlgebraicGeometry.range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/85a9ca56-a5bd-59f3-92a9-be126968e3ac
-- title:
--   Sections of a regular proper flat curve over a DVR land in the maximal smooth locus
-- statement:
--   Let $A$ be a commutative ring which is a domain and a discrete valuation ring, and let $C$ be an integral scheme (in the zeroth universe) equipped with a morphism $c : C \to \operatorname{Spec} A$ that is proper and flat. Assume $C$ is regular in the sense that for every point $x$ of $C$ the stalk $\mathcal{O}_{C,x}$ of the structure presheaf is a regular local ring. Let $U$ be an open subscheme of $C$ whose inclusion followed by $c$, i.e. the composite $U \hookrightarrow C \to \operatorname{Spec} A$, is smooth of relative dimension $1$; assume $U$ is maximal with this property, i.e. every open $W \subseteq C$ for which $W \hookrightarrow C \to \operatorname{Spec} A$ is smooth of relative dimension $1$ satisfies $W \le U$, and assume the underlying set of $U$ is non-empty. Finally let $\varepsilon$ be a section of $c$, that is (by the definition of `SchemeHomOver`) a morphism $\varepsilon : \operatorname{Spec} A \to C$ together with the identity $\varepsilon \text{ followed by } c = \mathrm{id}_{\operatorname{Spec} A}$. Then the set-theoretic range of the underlying continuous map of $\varepsilon$ is contained in the underlying set of $U$.
--
--   This is the standard statement that sections of a regular proper flat model over a discrete valuation ring factor through the smooth locus, here in the form that the image of a section lies inside the largest open on which the model is smooth of relative dimension one. It is used in the construction of the relative Picard/Néron-model input for the modular curve $X_1(Mp)$, where it supplies the hypothesis that a given section of a two-chart model lands in the smooth locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.range_subset_of_isRegularLocalRing_of_smoothOfRelativeDimension_maximal
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Spec (CommRingCat.of A)) [IsProper c] [Flat c]
    (hreg : ∀ x : C, IsRegularLocalRing (C.presheaf.stalk x))
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hUmax : ∀ W : C.Opens, SmoothOfRelativeDimension 1 (W.ι ≫ c) → W ≤ U) (hUne : (U : Set C).Nonempty)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c) :
    Set.range ε.1.base ⊆ (U : Set C) := by sorry
