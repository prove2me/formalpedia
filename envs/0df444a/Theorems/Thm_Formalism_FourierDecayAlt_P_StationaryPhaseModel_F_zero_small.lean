-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_zero_small
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_zero_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:03.623901+00:00
-- url     : https://prove2.me/theorems/d4aa4afe-e38d-4df6-b7e4-ed6085b20ba7
-- title:
--   Stationary Phase Model: F zero small
-- statement:
--   The Stationary Phase Model construction uses the F zero small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2994-L3099
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2994-L3099

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_zero_small (d : ℕ) (hd : 0 < d) (β : ℂ) (hβ : β ≠ 0) (r Λ : ℝ) (hr : 0 < r) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (g : (Fin d → ℂ) → ℂ) (dg : (Fin d → ℂ) → Fin d → ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 (2 * r)) → (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
        HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k)) →
      (∀ k, dg 0 k = 0) →
      (∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ 1 →
          ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) -
              (psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0‖ ≤ C * S * ‖t‖ ^ (d + 1) := by sorry
