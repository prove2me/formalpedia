-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_slope_bound_of_conditions
-- name    : Formalism.L2.Indef.Tree.slope_bound_of_conditions
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:51.331617+00:00
-- url     : https://prove2.me/theorems/d1386b8e-1bad-4382-b73b-bbaf084306bc
-- title:
--   Tree: slope bound of conditions
-- statement:
--   The Tree construction uses the slope bound of conditions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L732-L762
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L732-L762

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

theorem Formalism.L2.Indef.Tree.slope_bound_of_conditions {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {Bs : DefBase K}
    {Df : DefSide Bs} (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc)
    (hC1 : 0 ≤ C1) (hCm : 0 ≤ Cm) (S : IndefData Df) (Zs : IndefScale Bs) (CH : ℝ) (P : SlopeBoundParameters)
    (F : Bs.J → SlopeBoundLiftData K P) (XWr : ∀ j, InfinitePlace K → Matrix (Fin (S.dW j)) (Fin (S.dW j)) ℂ)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : ∀ j, FacParams Cf (F j)) (hDF : ∀ j, LeafDegFlat Cc (F j))
    (hEx : ∀ j, LeafExport Cf (F j)) (hCu : ∀ j, LeafCut (F j)) (hSB : ∀ j, LeafShareBad (F j))
    (hBR : ∀ j, LeafBadRows (F j)) (hMN : ∀ j, LeafMuN (F j)) (hLa : ∀ j, LeafLam (F j))
    (hRe : ∀ j, LeafRecord (XWr j) (S.M j) (F j)) (hN2 : ∀ j, LeafNote2 Cn (F j))
    (hMe : ∀ j, LeafMeasure Cm (D := S.D) (S.XW j) (XWr j) (S.M j) P)
    (hDef : ∀ j, (F j).q' = 0 → LeafDef C1 Cf (F j))
    (hRo : ∀ j, (F j).q' ≠ 0 → LeafRoot (F j)) (hFl : ∀ j, (F j).q' ≠ 0 → LeafFlat Cf (F j))
    (hDg : ∀ j, (F j).q' ≠ 0 → LeafDeg (F j)) (hRh : ∀ j, (F j).q' ≠ 0 → LeafRho (F j))
    (hSh : ∀ j, (F j).q' ≠ 0 → LeafShare (F j)) (hSm : ∀ j, (F j).q' ≠ 0 → LeafSmall (F j))
    (hMs : ∀ j, (F j).q' ≠ 0 → LeafMeans Ca Cb (F j)) (hHS : ∀ j, (F j).q' ≠ 0 → LeafHS (F j))
    (hSu : ∀ j, (F j).q' ≠ 0 → LeafSum (F j)) (hI13 : ∀ j, (F j).q' ≠ 0 → CrudeSizeBound (F j))
    (hEp : ∀ j, (F j).q' ≠ 0 → LeafEps (F j)) (hDs : ∀ j, (F j).q' ≠ 0 → LeafDescent (F j))
    (hPh : ∀ j, (F j).q' ≠ 0 → LeafPh (F j)) (hGm : ∀ j, (F j).q' ≠ 0 → LeafGmin (F j))
    (hCP : ∀ j, (F j).q' ≠ 0 → CompParams Ca Cb (F j))
    (hD : 0 < S.D) (hdW : ∀ j, S.dW j = S.D) (hF : S.Frames) (hT : ScaleTies Zs P F) :
    S.L3 (Zs.num (slopeBoundConstant Ca Cb Cf Cc C1 Cm) CH) := by sorry
