-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_scaleTies_unique_def
-- name    : Formalism.L2.Indef.Tree.scaleTies_unique_def
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:49:16.894802+00:00
-- url     : https://prove2.me/theorems/0937af7d-9731-5325-94d3-5858be69cefe
-- title:
--   Tree: scale Ties unique def
-- statement:
--   The Tree construction uses the scale Ties unique def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L701-L718
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L701-L718

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι

theorem Formalism.L2.Indef.Tree.scaleTies_unique_def {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Zs : IndefScale Bs)
    (P : SlopeBoundParameters) (F : Bs.J → SlopeBoundLiftData K P) (hT : ScaleTies Zs P F) (hm : 1 ≤ P.m) :
    ∃! j, (F j).q' = 0 := by sorry
