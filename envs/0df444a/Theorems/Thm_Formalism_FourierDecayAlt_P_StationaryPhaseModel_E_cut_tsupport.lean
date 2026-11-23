-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_tsupport
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_tsupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:25.658274+00:00
-- url     : https://prove2.me/theorems/9da7ce87-6db5-4412-9846-0b2399341097
-- title:
--   Stationary Phase Model: E cut tsupport
-- statement:
--   The Stationary Phase Model construction uses the E cut tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1751-L1753
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1751-L1753

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
variable {d : ℕ} {ρ : ℝ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_tsupport (hρ : 0 < ρ) : tsupport (cutB d ρ) = Metric.closedBall (0 : Fin d → ℂ) ρ := by sorry
