-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_slope_bound_single_lift_of_definitions
-- name    : Formalism.L2.Indef.Tree.slope_bound_single_lift_of_definitions
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:07.832189+00:00
-- url     : https://prove2.me/theorems/1cb72722-f2e9-4788-9d9a-957035d04433
-- title:
--   Tree: slope bound single lift of definitions
-- statement:
--   The Tree construction uses the slope bound single lift of definitions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L481-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L481-L558

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_main
import Theorems.Thm_UpperTheory_Reformulated_B_SelectionLemmas_main

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
set_option maxHeartbeats 1000000

theorem Formalism.L2.Indef.Tree.slope_bound_single_lift_of_definitions {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hC1 : 0 ≤ C1)
    (hCm : 0 ≤ Cm) (d D : ℕ) (hD : 0 < D) (hdD : d = D) (XW XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (M : Submodule (𝓞 K) (Fin d → K)) (hM : Submodule.IsLattice K M) (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : FacParams Cf F) (hDF : LeafDegFlat Cc F) (hEx : LeafExport Cf F)
    (hCu : LeafCut F) (hSB : LeafShareBad F) (hBR : LeafBadRows F) (hMN : LeafMuN F) (hLa : LeafLam F)
    (hRe : LeafRecord XWr M F) (hN2 : LeafNote2 Cn F) (hMe : LeafMeasure Cm (D := D) XW XWr M P)
    (hq : F.q' = 0) (hDe : LeafDef C1 Cf F) :
    Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ F.main + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx) := by sorry
