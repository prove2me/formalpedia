-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_holo_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.holo_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:59.583983+00:00
-- url     : https://prove2.me/theorems/eb9e139f-69de-4aba-bdd1-5c3dcb35a78d
-- title:
--   Stationary Phase Model: holo bound
-- statement:
--   The Stationary Phase Model construction uses the holo bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L900-L955
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L900-L955

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.holo_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (i : ℕ) {f : E → F} {x : E} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (Metric.ball x ((i + 1 : ℕ) * δ)))
    (hM : ∀ y ∈ Metric.ball x ((i + 1 : ℕ) * δ), ‖f y‖ ≤ M) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ M / δ ^ i := by sorry
