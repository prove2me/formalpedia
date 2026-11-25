-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_model_integral_first_error
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.model_integral_first_error
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:18.14725+00:00
-- url     : https://prove2.me/theorems/a8c4f0cc-ae4b-4cea-810b-a59b0822562e
-- title:
--   Stationary Phase Model: model integral first error
-- statement:
--   The Stationary Phase Model construction uses the model integral first error property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2310-L2382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2310-L2382

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.model_integral_first_error {C : ℝ} (hβ : β ≠ 0) (hOB : E_OB d 2 β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hΓ : 0 < Γ) (hph : E_Phase d r Γ c₁ φ) (hρ0 : 0 < ρ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCχ : 0 ≤ Cχ) (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) :
    ‖∫ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ a₀ ℓ x) ∂(muPi β (Fin d))‖ ≤
      2 * (C * (2 ^ (d + 1 + 2) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) *
        (2 ^ (d + 1 + 2) * (Cχ * (ρ + 1) ^ (d + 1 + 2)) * S)) * τ ^ (d + 2)) := by sorry
