-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_smul_tsupport
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_smul_tsupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:50.402132+00:00
-- url     : https://prove2.me/theorems/72692dd6-8fcb-4f3c-8ddc-136fd8a52787
-- title:
--   Stationary Phase Model: E cut smul tsupport
-- statement:
--   The Stationary Phase Model construction uses the E cut smul tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2222-L2224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2222-L2224

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_smul_tsupport (hρ : 0 < ρ) (g : (Fin d → ℂ) → V) :
    tsupport (fun x => cutB d ρ x • g x) ⊆ Metric.closedBall (0 : Fin d → ℂ) ρ := by sorry
