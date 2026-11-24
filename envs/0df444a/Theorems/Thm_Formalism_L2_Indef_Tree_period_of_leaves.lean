-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_period_of_leaves
-- name    : Formalism.L2.Indef.Tree.period_of_leaves
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:43.125188+00:00
-- url     : https://prove2.me/theorems/454940a7-11de-4a4b-9676-18b5700fcd49
-- title:
--   Tree: period of leaves
-- statement:
--   The Tree construction uses the period of leaves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L452-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L452-L460

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

theorem Formalism.L2.Indef.Tree.period_of_leaves (P : SlopeBoundParameters) (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P)
    (hNo : LeafNorm P) (hv : 0 < P.v) (hrd : 2 * P.v = P.rd) (h4 : 4 ≤ P.rd) (hLc : |P.Lc| ≤ P.L)
    (hx : 1 ≤ P.x) :
    P.logOm = Real.eulerMascheroniConstant + Real.log (Real.pi / P.v) - P.Lc ∧ |P.logOm| ≤ P.La := by sorry
