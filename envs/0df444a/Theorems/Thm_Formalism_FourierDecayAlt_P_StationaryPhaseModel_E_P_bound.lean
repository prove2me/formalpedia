-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:06.313767+00:00
-- url     : https://prove2.me/theorems/18f41201-54d5-4903-9b56-25a8c6df0b84
-- title:
--   Stationary Phase Model: E P bound
-- statement:
--   The Stationary Phase Model construction uses the E P bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1901-L1913
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1901-L1913

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_P_bound {φ : E → ℝ} {n : ℕ} (h2n : 2 ≤ n) (hφ : ContDiff ℝ n φ) {r Γ : ℝ} (hr : 0 < r)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ n →
      ‖iteratedFDeriv ℝ i (E_P φ) x‖ ≤ Γ + Γ * (r + 1) ^ 2 := by sorry
