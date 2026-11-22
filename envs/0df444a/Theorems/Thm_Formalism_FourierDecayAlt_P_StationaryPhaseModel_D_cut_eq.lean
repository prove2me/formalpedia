-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_eq
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_cut_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:25.925548+00:00
-- url     : https://prove2.me/theorems/95ad8430-64da-405b-9e45-32fd98c47283
-- title:
--   Stationary Phase Model: D cut eq
-- statement:
--   The Stationary Phase Model construction uses the D cut eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1174-L1177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1174-L1177

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_cut_eq (d : ℕ) {ρ : ℝ} (h : 0 < ρ) :
    cutB d ρ = (⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ : ContDiffBump (0 : Fin d → ℂ)) := by sorry
