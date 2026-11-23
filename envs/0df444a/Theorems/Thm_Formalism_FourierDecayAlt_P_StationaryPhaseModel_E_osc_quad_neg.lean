-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_osc_quad_neg
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_osc_quad_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:26.216465+00:00
-- url     : https://prove2.me/theorems/59ad9975-7697-4c2b-88f8-9a4e3128dc0b
-- title:
--   Stationary Phase Model: E osc quad neg
-- statement:
--   The Stationary Phase Model construction uses the E osc quad neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2247-L2249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2247-L2249

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_osc_quad_neg (φ : (Fin d → ℂ) → ℝ) (τ : ℝ) (x : Fin d → ℂ) :
    osc (quad φ) τ (-x) = osc (quad φ) τ x := by sorry
