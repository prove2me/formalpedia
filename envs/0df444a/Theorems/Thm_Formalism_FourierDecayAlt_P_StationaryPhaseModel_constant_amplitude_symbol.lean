-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_constant_amplitude_symbol
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.constant_amplitude_symbol
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:58.614937+00:00
-- url     : https://prove2.me/theorems/3573b16e-171c-4925-9801-be9f4659d94d
-- title:
--   Stationary Phase Model: constant amplitude symbol
-- statement:
--   The Stationary Phase Model construction uses the constant amplitude symbol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2183-L2190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2183-L2190

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
variable {d : ℕ} {β : ℂ} {ρ : ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.constant_amplitude_symbol (hρ : 0 < ρ) {N : ℕ} {Cχ : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ) {r' σ : ℝ} (hr' : 0 < r') (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) {a₀ : V} {S : ℝ} (ha : ‖a₀‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 0 N (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (constantAmplitude d ρ a₀) := by sorry
