-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_one_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_one_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:34.72255+00:00
-- url     : https://prove2.me/theorems/2de0f93b-45a8-479f-9e1b-3c9223c7b506
-- title:
--   Stationary Phase Model: D gau one bound
-- statement:
--   The Stationary Phase Model construction uses the D gau one bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1032-L1064
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1032-L1064

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
noncomputable section

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_one_bound (d n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Fin d → ℂ,
    (1 + ‖x‖) ^ n * ‖iteratedFDeriv ℝ n (D_gau d 1) x‖ ≤ M := by sorry
