-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_u_support
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_u_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:50.889413+00:00
-- url     : https://prove2.me/theorems/13ea2c64-2261-4003-9709-6e8bd2d39ad5
-- title:
--   Stationary Phase Model: E u support
-- statement:
--   The Stationary Phase Model construction uses the E u support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2404-L2417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2404-L2417

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_u_support (hρ0 : 0 < ρ) (hρr : ρ ≤ r) {a : (Fin d → ℂ) → V}
    (hsupp : Function.support a ⊆ Metric.closedBall 0 r) :
    Function.support (E_u d ρ a) ⊆ Metric.closedBall 0 r := by sorry
