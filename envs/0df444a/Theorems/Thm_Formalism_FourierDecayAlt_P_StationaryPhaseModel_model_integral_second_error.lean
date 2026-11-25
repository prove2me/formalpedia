-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_model_integral_second_error
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.model_integral_second_error
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:25.173003+00:00
-- url     : https://prove2.me/theorems/e46aa6c3-e667-4a6c-b737-453a6e871b69
-- title:
--   Stationary Phase Model: model integral second error
-- statement:
--   The Stationary Phase Model construction uses the model integral second error property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2273-L2294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2273-L2294

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.model_integral_second_error {C : ℝ} (hOB : E_OB d 3 β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hΓ : 0 < Γ) (hph : E_Phase d r Γ c₁ φ) (hρ0 : 0 < ρ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCχ : 0 ≤ Cχ) (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖∫ x, osc (fun y => quad φ y + s * E_P φ y) τ x • ((E_P φ x * E_P φ x) • modelAmplitude d ρ a₀ ℓ x)
        ∂(muPi β (Fin d))‖ ≤
      C * (2 ^ (d + 1 + 3) * (2 ^ (d + 1 + 3) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) *
        ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6))) *
        (2 ^ (d + 1 + 3) * (Cχ * (ρ + 1) ^ (d + 1 + 3)) * (ρ + 2) * S)) * τ ^ (d + 3) := by sorry
