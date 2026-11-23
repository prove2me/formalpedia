-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_mem_ball
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_mem_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:52.83085+00:00
-- url     : https://prove2.me/theorems/091a1c14-efcf-4d72-b54a-98f08b187b03
-- title:
--   Stationary Phase Model: F mem ball
-- statement:
--   The Stationary Phase Model construction uses the F mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2833-L2837
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2833-L2837

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
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_mem_ball (hr : 0 < r) {x : Fin d → ℂ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) :
    x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4) := by sorry
