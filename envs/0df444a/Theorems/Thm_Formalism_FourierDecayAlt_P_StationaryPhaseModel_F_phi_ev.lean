-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_ev
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:56.609406+00:00
-- url     : https://prove2.me/theorems/7a286397-44b3-4a56-8e1c-8a38b81a53e3
-- title:
--   Stationary Phase Model: F phi ev
-- statement:
--   The Stationary Phase Model construction uses the F phi ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2819-L2822
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2819-L2822

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_ev (hr : 0 < r) (c : ℂ) {x : Fin d → ℂ} (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4)) :
    F_phi d r c g =ᶠ[𝓝 x] (realPartMulCLM c ∘ g) := by sorry
