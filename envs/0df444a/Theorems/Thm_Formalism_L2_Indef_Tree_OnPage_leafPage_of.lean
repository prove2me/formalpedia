-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_OnPage_leafPage_of
-- name    : Formalism.L2.Indef.Tree.OnPage.leafPage_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:20.989192+00:00
-- url     : https://prove2.me/theorems/702bb7ca-fd2c-5cc5-904c-2e3e0f5c35d0
-- title:
--   On Page: leaf Page of
-- statement:
--   The On Page construction uses the leaf Page of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L451-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L451-L477

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

theorem Formalism.L2.Indef.Tree.OnPage.leafPage_of (O : OnObj S P c) (hC : ConstC c) (hx : 3 ≤ O.x) (hN4 : HalfDegreeAtLeastFour O) (h12 : PrimeCongruenceConditions O)
    (h1246 : DegreeAtLeastFortyFour O) (h29 : DimensionExceedsDegreeByThree O) (h1 : LeafSZ1 O) (hSg : LeafSign O) (h75 : ConductorCongruentPrimePair O)
    (tVd : TieVd O) (tBp : TieBp O) (tNc : TieNc O) : LeafPage O := by sorry
