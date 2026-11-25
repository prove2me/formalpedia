-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_leafSizes_of_page
-- name    : Formalism.L2.Indef.Tree.OnPage.leafSizes_of_page
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:48:39.05878+00:00
-- url     : https://prove2.me/theorems/56a0d655-871d-5be4-af5c-398b7ecef21c
-- title:
--   On Page: leaf Sizes of page
-- statement:
--   The On Page construction uses the leaf Sizes of page property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L319-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L319-L442

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}
set_option maxHeartbeats 1000000

theorem Formalism.L2.Indef.Tree.OnPage.leafSizes_of_page (O : OnObj S P c) (C2 : ℝ) (hC2 : 0 ≤ C2) (hC : 1 ≤ c.C)
    (hx : 3 ≤ O.x) (hxC : 3 * c.C * C2 ≤ O.x)
    (hEps : ExponentSmallBound O) (hN4 : HalfDegreeAtLeastFour O) (h1246 : DegreeAtLeastFortyFour O) (h29 : DimensionExceedsDegreeByThree O) (h21 : RankAndLengthLowerBounds O) (hW : LeafW O)
    (h14 : SupportGapBounds O) (h011 : EtaPowerBound O) (hSg : LeafSign O) (h1243 : NodeCountBound O) (h13 : DiscriminantDegreeBound O)
    (h231 : ProductLowerBoundTwist O) (h44 : TwistDensityBounds O) (tX2 : SecondRatioDefinition O) (tZ3 : TimeDiscriminantBound O C2) : LeafSizes O := by sorry
