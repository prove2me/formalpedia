-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_leafBad_of_page
-- name    : Formalism.L2.Indef.Tree.OnPage.leafBad_of_page
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:15.211646+00:00
-- url     : https://prove2.me/theorems/4d8e30e9-a8fc-5b24-8f7a-ee12e25865c2
-- title:
--   On Page: leaf Bad of page
-- statement:
--   The On Page construction uses the leaf Bad of page property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L226-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L226-L276

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

theorem Formalism.L2.Indef.Tree.OnPage.leafBad_of_page (O : OnObj S P c)
    (hC : 0 ≤ c.C) (hCb1 : 14 ≤ c.Cb1) (hCb2 : 66 * c.C + 4 ≤ c.Cb2) (hx : 3 ≤ O.x)
    (hEps : ExponentSmallBound O) (hN4 : HalfDegreeAtLeastFour O) (h1246 : DegreeAtLeastFortyFour O) (h21 : RankAndLengthLowerBounds O) (h1 : LeafSZ1 O) (hW : LeafW O)
    (h14 : SupportGapBounds O) (h121 : LogPrimeProductBound O) (h1232 : ProductWithRatioBound O) (h75 : ConductorCongruentPrimePair O) (h19 : SquaredTimeBound O) (h18 : PowerTwelveBound O)
    (tVd : TieVd O) : LeafBad O := by sorry
