-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_diff_fderiv
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_diff_fderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:46.639515+00:00
-- url     : https://prove2.me/theorems/41f7c682-9ce2-4c22-a56d-594b832b5eab
-- title:
--   Stationary Phase Model: F diff fderiv
-- statement:
--   The Stationary Phase Model construction uses the F diff fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2613-L2618
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2613-L2618

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
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {r : ℝ} {g : (Fin d → ℂ) → ℂ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_diff_fderiv (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) :
    DifferentiableOn ℂ (fderiv ℂ g) (Metric.ball 0 (2 * r)) := by sorry
