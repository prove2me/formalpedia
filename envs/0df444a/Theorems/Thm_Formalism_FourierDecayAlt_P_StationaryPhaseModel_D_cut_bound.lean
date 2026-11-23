-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_cut_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:05.263265+00:00
-- url     : https://prove2.me/theorems/e8542e28-591d-411a-8be9-0d19b4e7db64
-- title:
--   Stationary Phase Model: D cut bound
-- statement:
--   The Stationary Phase Model construction uses the D cut bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1203-L1211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1203-L1211

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_cut_bound (d N : ℕ) {ρ : ℝ} (h : 0 < ρ) : ∃ M : ℝ, ∀ x, ∀ i ≤ N,
    ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ M := by sorry
