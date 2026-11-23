-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_ph_fderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:29.756742+00:00
-- url     : https://prove2.me/theorems/3edefc3f-beb3-4408-80fc-f55a700cb649
-- title:
--   Stationary Phase Model: E ph fderiv
-- statement:
--   The Stationary Phase Model construction uses the E ph fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1995-L2005
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1995-L2005

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_ph_fderiv {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (s : ℝ) :
    fderiv ℝ (fun y => quad φ y + s * E_P φ y) =
      fun x => (1 - s) • (fderiv ℝ (fderiv ℝ φ) 0 x) + s • fderiv ℝ φ x := by sorry
