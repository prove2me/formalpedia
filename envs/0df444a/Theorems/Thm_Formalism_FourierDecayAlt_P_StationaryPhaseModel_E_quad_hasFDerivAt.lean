-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_hasFDerivAt
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_quad_hasFDerivAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:55.222796+00:00
-- url     : https://prove2.me/theorems/c9387b99-37dd-4daa-a8d5-f6204d41072b
-- title:
--   Stationary Phase Model: E quad has FDeriv At
-- statement:
--   The Stationary Phase Model construction uses the E quad has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1784-L1791
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1784-L1791

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_quad_hasFDerivAt {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) :
    HasFDerivAt (quad φ) (fderiv ℝ (fderiv ℝ φ) 0 x) x := by sorry
