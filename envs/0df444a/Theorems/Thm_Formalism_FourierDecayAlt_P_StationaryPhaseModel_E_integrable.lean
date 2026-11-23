-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_integrable
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:56.150227+00:00
-- url     : https://prove2.me/theorems/63cea110-02a0-4ac1-acc2-01c8c3f726a9
-- title:
--   Stationary Phase Model: E integrable
-- statement:
--   The Stationary Phase Model construction uses the E integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2296-L2300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2296-L2300

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_integrable (hβ : β ≠ 0) {ψ : (Fin d → ℂ) → ℝ} (hψ : Continuous ψ) (τ : ℝ) {g : (Fin d → ℂ) → V}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => osc ψ τ x • g x) (muPi β (Fin d)) := by sorry
