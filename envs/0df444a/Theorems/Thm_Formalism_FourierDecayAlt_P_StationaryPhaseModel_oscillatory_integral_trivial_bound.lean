-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_oscillatory_integral_trivial_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.oscillatory_integral_trivial_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:37.443187+00:00
-- url     : https://prove2.me/theorems/751bbc29-f4b4-4774-83d0-59c77825ed71
-- title:
--   Stationary Phase Model: oscillatory integral trivial bound
-- statement:
--   The Stationary Phase Model construction uses the oscillatory integral trivial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L3150-L3169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L3150-L3169

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
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.oscillatory_integral_trivial_bound (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (r : ℝ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (u : (Fin d → ℂ) → ℂ) (hu : ∀ x, ‖u x‖ = 1) (a : (Fin d → ℂ) → V) (S : ℝ)
    (hsupp : Function.support a ⊆ Metric.closedBall 0 r) (hS : ∀ x, ‖a x‖ ≤ S) :
    ‖∫ x : Fin d → ℂ, u x • a x ∂(muPi β (Fin d))‖ ≤
      S * (muPi β (Fin d) (Metric.closedBall 0 r)).toReal := by sorry
