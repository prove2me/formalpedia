-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_dphi_sym
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_dphi_sym
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:27.08745+00:00
-- url     : https://prove2.me/theorems/8f53082b-40e4-45f7-a366-6e093bc0e78f
-- title:
--   Stationary Phase Model: E dphi sym
-- statement:
--   The Stationary Phase Model construction uses the E dphi sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2013-L2026
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2013-L2026

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_dphi_sym {φ : E → ℝ} {N : ℕ} (hN : 1 ≤ N) (hφ : ContDiff ℝ (N + 1 : ℕ) φ) {r Γ σ : ℝ} (hr : 0 < r)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : fderiv ℝ φ 0 = 0)
    (hb : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N + 1 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) 1 N (Γ * (r + 1) ^ N) (fderiv ℝ φ) := by sorry
