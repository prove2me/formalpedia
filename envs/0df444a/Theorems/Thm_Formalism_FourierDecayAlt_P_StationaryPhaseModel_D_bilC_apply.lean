-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_bilC_apply
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_bilC_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:32.207917+00:00
-- url     : https://prove2.me/theorems/79ce269c-6367-487a-b2e4-ec19f487fb61
-- title:
--   Stationary Phase Model: D bil C apply
-- statement:
--   The Stationary Phase Model construction uses the D bil C apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1337-L1339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1337-L1339

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_bilC_apply (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) (x v : Fin d → ℂ) :
    D_bilC d c H Γ hΓ hH x v = (c * (v ⬝ᵥ (H *ᵥ x))).re := by sorry
