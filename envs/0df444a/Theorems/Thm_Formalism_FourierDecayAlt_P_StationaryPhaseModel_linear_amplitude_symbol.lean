-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_linear_amplitude_symbol
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.linear_amplitude_symbol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:02.358601+00:00
-- url     : https://prove2.me/theorems/2079f786-225a-4322-83ec-a48f341141f5
-- title:
--   Stationary Phase Model: linear amplitude symbol
-- statement:
--   The Stationary Phase Model construction uses the linear amplitude symbol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2192-L2199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2192-L2199

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.linear_amplitude_symbol (hρ : 0 < ρ) {N : ℕ} {Cχ : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ) {r' σ : ℝ} (hr' : 0 < r') (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) {ℓ : (Fin d → ℂ) →L[ℝ] V} {S : ℝ} (hl : ‖ℓ‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 1 N (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (linearAmplitude d ρ ℓ) := by sorry
