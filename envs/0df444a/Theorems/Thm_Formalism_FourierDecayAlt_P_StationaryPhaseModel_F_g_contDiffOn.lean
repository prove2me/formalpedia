-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_g_contDiffOn
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_g_contDiffOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:00.566291+00:00
-- url     : https://prove2.me/theorems/4056d817-2d31-4340-b3e5-0940608eb4a0
-- title:
--   Stationary Phase Model: F g cont Diff On
-- statement:
--   The Stationary Phase Model construction uses the F g cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2810-L2812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2810-L2812

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_g_contDiffOn (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (n : ℕ) :
    ContDiffOn ℝ n g (Metric.ball 0 (2 * r)) := by sorry
