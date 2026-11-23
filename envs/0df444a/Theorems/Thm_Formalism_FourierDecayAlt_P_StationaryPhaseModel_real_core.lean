-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_real_core
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.real_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:13.273249+00:00
-- url     : https://prove2.me/theorems/53cc80d8-61dd-4da0-a303-7dae0bc0d8ed
-- title:
--   Stationary Phase Model: real core
-- statement:
--   The Stationary Phase Model construction uses the real core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2465-L2557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2465-L2557

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.real_core (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (r Γ c₁ : ℝ) (hr : 0 < r) (hΓ : 0 < Γ) (hc₁ : 0 < c₁) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ C : ℝ, ∀ (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ → τ ≤ 1 →
      ContDiff ℝ (d + 6 : ℕ) φ →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ d + 6 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) →
      fderiv ℝ φ 0 = 0 →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ‖∫ x, osc φ τ x • a x ∂(muPi β (Fin d)) -
            (∫ x, osc (quad φ) τ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))) • a 0‖ ≤ C * S * τ ^ (d + 1) := by sorry
