-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_snd
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_snd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:00.486548+00:00
-- url     : https://prove2.me/theorems/92740f4c-86cb-4075-8abb-7186b87563b2
-- title:
--   Stationary Phase Model: F phi snd
-- statement:
--   The Stationary Phase Model construction uses the F phi snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2865-L2882
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2865-L2882

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_snd (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) (u v : Fin d → ℂ) :
    fderiv ℝ (fderiv ℝ (F_phi d r c g)) 0 u v = (c * fderiv ℂ (fderiv ℂ g) 0 u v).re := by sorry
