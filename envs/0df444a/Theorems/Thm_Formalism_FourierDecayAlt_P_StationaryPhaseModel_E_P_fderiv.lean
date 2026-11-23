-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_fderiv
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_fderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:04.281254+00:00
-- url     : https://prove2.me/theorems/eee3a336-a1f8-4be9-b3b6-722abcaad8d3
-- title:
--   Stationary Phase Model: E P fderiv
-- statement:
--   The Stationary Phase Model construction uses the E P fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1852-L1855
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1852-L1855

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_fderiv {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) :
    fderiv ℝ (E_P φ) = fun x => fderiv ℝ φ x - fderiv ℝ (fderiv ℝ φ) 0 x := by sorry
