-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_C_line_hasDerivAt
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.C_line_hasDerivAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:45.128233+00:00
-- url     : https://prove2.me/theorems/9bebfe24-76ad-40ff-a9ad-0cd8392cfb8c
-- title:
--   Stationary Phase Model: C line has Deriv At
-- statement:
--   The Stationary Phase Model construction uses the C line has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L735-L739
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L735-L739

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
open MeasureTheory Filter Topology Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.C_line_hasDerivAt {f : E → F} {y v : E} {ζ : ℂ} (h : DifferentiableAt ℂ f (y + ζ • v)) :
    HasDerivAt (fun z : ℂ => f (y + z • v)) (fderiv ℂ f (y + ζ • v) v) ζ := by sorry
