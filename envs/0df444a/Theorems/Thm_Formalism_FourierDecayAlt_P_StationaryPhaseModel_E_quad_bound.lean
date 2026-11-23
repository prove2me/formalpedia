-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_quad_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:35.171253+00:00
-- url     : https://prove2.me/theorems/4e0023ff-b47d-496a-ad6c-7acb3527cbd7
-- title:
--   Stationary Phase Model: E quad bound
-- statement:
--   The Stationary Phase Model construction uses the E quad bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1815-L1847
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1815-L1847

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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_quad_bound {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {r Γ : ℝ} (hr : 0 < r) (h0 : ‖φ 0‖ ≤ Γ)
    (h2 : ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ Γ) (i : ℕ) {x : E} (hx : x ∈ Metric.closedBall (0 : E) r) :
    ‖iteratedFDeriv ℝ i (quad φ) x‖ ≤ Γ * (r + 1) ^ 2 := by sorry
