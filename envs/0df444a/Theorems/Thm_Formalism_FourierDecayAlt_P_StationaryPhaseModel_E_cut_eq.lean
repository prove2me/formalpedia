-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_eq
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:19.753197+00:00
-- url     : https://prove2.me/theorems/7011a383-f94c-4e74-83cb-5468bc76af10
-- title:
--   Stationary Phase Model: E cut eq
-- statement:
--   The Stationary Phase Model construction uses the E cut eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1738-L1740
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1738-L1740

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
variable {d : ℕ} {ρ : ℝ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_eq (hρ : 0 < ρ) : cutB d ρ = (E_bump d ρ hρ : (Fin d → ℂ) → ℝ) := by sorry
