-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_hasFDerivAt_osc
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_hasFDerivAt_osc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:48.80212+00:00
-- url     : https://prove2.me/theorems/413ed3b1-c39f-4771-a687-3af62576a891
-- title:
--   Stationary Phase Model: B has FDeriv At osc
-- statement:
--   The Stationary Phase Model construction uses the B has FDeriv At osc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L444-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L444-L454

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_hasFDerivAt_osc {φ : E → ℝ} (τ : ℝ) {x : E} (hφ : DifferentiableAt ℝ φ x) :
    HasFDerivAt (osc φ τ)
      ((Complex.I * osc φ τ x) • (Complex.ofRealCLM.comp (τ⁻¹ • fderiv ℝ φ x))) x := by sorry
