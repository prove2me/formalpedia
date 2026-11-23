-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_symm
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:56.724985+00:00
-- url     : https://prove2.me/theorems/69b4963a-478d-40e8-81c4-44e818442117
-- title:
--   Stationary Phase Model: F symm
-- statement:
--   The Stationary Phase Model construction uses the F symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2628-L2633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2628-L2633

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_symm (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (u v : Fin d → ℂ) :
    fderiv ℂ (fderiv ℂ g) 0 u v = fderiv ℂ (fderiv ℂ g) 0 v u := by sorry
