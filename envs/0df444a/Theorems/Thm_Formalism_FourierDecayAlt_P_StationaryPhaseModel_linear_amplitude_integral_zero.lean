-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_linear_amplitude_integral_zero
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.linear_amplitude_integral_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:14.225952+00:00
-- url     : https://prove2.me/theorems/e484c0b1-79a8-483b-9e19-a2adbc65eecf
-- title:
--   Stationary Phase Model: linear amplitude integral zero
-- statement:
--   The Stationary Phase Model construction uses the linear amplitude integral zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2304-L2308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2304-L2308

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
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.linear_amplitude_integral_zero (hβ : β ≠ 0) (hρ0 : 0 < ρ) :
    ∫ x, osc (quad φ) τ x • linearAmplitude d ρ ℓ x ∂(muPi β (Fin d)) = 0 := by sorry
