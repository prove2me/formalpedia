-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_example_slope_bound_nontrivial
-- name    : Formalism.L2.Indef.Tree.example_slope_bound_nontrivial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:54.783808+00:00
-- url     : https://prove2.me/theorems/11ef86ea-3371-4874-8475-d73195a3c517
-- title:
--   Tree: example slope bound nontrivial
-- statement:
--   The Tree construction uses the example slope bound nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L940-L947
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L940-L947

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

theorem Formalism.L2.Indef.Tree.example_slope_bound_nontrivial (v0 : InfinitePlace Examples₂.K3) :
    ∃ N : IndefNum (Examples₂.one.base Examples₂.K3 v0), ¬ (Examples₂.one.dat Examples₂.K3 v0).L3 N := by sorry
