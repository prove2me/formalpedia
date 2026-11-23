-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_iteratedFDeriv_comp_neg
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_iteratedFDeriv_comp_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:21.194478+00:00
-- url     : https://prove2.me/theorems/f37f6efe-6ea0-4328-ad4b-53491d3489a4
-- title:
--   Stationary Phase Model: E iterated FDeriv comp neg
-- statement:
--   The Stationary Phase Model construction uses the E iterated FDeriv comp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1875-L1887
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1875-L1887

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_iteratedFDeriv_comp_neg {f : E → F} {n : ℕ} (hf : ContDiff ℝ n f) {i : ℕ} (hi : i ≤ n) (x : E) :
    iteratedFDeriv ℝ i (fun y => f (-y)) x = (-1 : ℝ) ^ i • iteratedFDeriv ℝ i f (-x) := by sorry
