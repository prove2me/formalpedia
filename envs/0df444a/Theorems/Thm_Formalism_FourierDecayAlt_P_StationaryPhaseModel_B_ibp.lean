-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_ibp
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_ibp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:43.432063+00:00
-- url     : https://prove2.me/theorems/c1a5b797-aed8-4825-9cb2-51b997f38149
-- title:
--   Stationary Phase Model: B ibp
-- statement:
--   The Stationary Phase Model construction uses the B ibp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L465-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L465-L488

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_ibp {φ : E → ℝ} (τ : ℝ) (hφ : ContDiff ℝ 1 φ) {c : E → V} (hc : ContDiff ℝ 1 c)
    (hcs : HasCompactSupport c) (v : E) :
    ∫ x, osc φ τ x • fderiv ℝ c x v ∂μ =
      -∫ x, (Complex.I * osc φ τ x * ((τ⁻¹ * fderiv ℝ φ x v : ℝ) : ℂ)) • c x ∂μ := by sorry
