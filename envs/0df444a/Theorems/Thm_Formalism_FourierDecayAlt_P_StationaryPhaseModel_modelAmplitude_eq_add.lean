-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_modelAmplitude_eq_add
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.modelAmplitude_eq_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:19.084352+00:00
-- url     : https://prove2.me/theorems/45976ba6-1ab4-4f52-b35a-4fdd489ed36f
-- title:
--   Stationary Phase Model: model Amplitude eq add
-- statement:
--   The Stationary Phase Model construction uses the model Amplitude eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2170-L2173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2170-L2173

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.modelAmplitude_eq_add (a₀ : V) (ℓ : (Fin d → ℂ) →L[ℝ] V) :
    modelAmplitude d ρ a₀ ℓ = fun x => constantAmplitude d ρ a₀ x + linearAmplitude d ρ ℓ x := by sorry
