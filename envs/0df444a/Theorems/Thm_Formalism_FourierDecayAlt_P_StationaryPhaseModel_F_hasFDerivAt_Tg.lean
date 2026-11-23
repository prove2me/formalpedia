-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_hasFDerivAt_Tg
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_hasFDerivAt_Tg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:59.290968+00:00
-- url     : https://prove2.me/theorems/2f54fd60-9ee3-4eab-924f-ec4822f54a1d
-- title:
--   Stationary Phase Model: F has FDeriv At Tg
-- statement:
--   The Stationary Phase Model construction uses the F has FDeriv At Tg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2852-L2856
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2852-L2856

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_hasFDerivAt_Tg (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r)) :
    HasFDerivAt (realPartMulCLM c ∘ g) ((realPartMulCLM c).comp ((fderiv ℂ g x).restrictScalars ℝ)) x := by sorry
