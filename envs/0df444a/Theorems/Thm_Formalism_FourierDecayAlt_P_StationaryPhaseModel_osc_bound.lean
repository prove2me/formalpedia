-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_osc_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.osc_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:37.499215+00:00
-- url     : https://prove2.me/theorems/4d0eeba7-a783-4e33-97fb-eab847fc9867
-- title:
--   Stationary Phase Model: osc bound
-- statement:
--   The Stationary Phase Model construction uses the osc bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L658-L719
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L658-L719

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.osc_bound (d q : ℕ) (β : ℂ) (hβ : β ≠ 0) (Γ c₁ : ℝ) (hc₁ : 0 < c₁) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : Set (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ →
      ContDiff ℝ (d + 2 + q : ℕ) φ →
      Sym A (wt (Real.sqrt τ)) 1 (d + 1 + q) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ),
        0 ≤ K → HasCompactSupport b → tsupport b ⊆ A →
        Sym A (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b →
        ‖∫ x, osc φ τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q) := by sorry
