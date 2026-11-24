-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_cfl_Q
-- name    : Formalism.L2.Indef.Tree.cfl_Q
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:16.563226+00:00
-- url     : https://prove2.me/theorems/bb61c457-aba0-4408-880e-c7e7f636f68b
-- title:
--   Tree: cfl Q
-- statement:
--   The Tree construction uses the cfl Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L472-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L472-L474

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

theorem Formalism.L2.Indef.Tree.cfl_Q (E CfL PPp kap lrdk : ℝ) (hE : |E| ≤ PPp * kap) (h0 : 0 ≤ CfL) (h1 : CfL ≤ kap) (hl : 0 ≤ lrdk) :
    |2 * (E - CfL)| ≤ 2 * (PPp * kap) + 2 * kap + 2 * lrdk := by sorry
