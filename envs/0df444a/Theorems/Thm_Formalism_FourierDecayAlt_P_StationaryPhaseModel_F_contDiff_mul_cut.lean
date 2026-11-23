-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_contDiff_mul_cut
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_contDiff_mul_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:56.635734+00:00
-- url     : https://prove2.me/theorems/e7eb7ac6-07ac-4476-addb-6a7682faf148
-- title:
--   Stationary Phase Model: F cont Diff mul cut
-- statement:
--   The Stationary Phase Model construction uses the F cont Diff mul cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2584-L2595
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2584-L2595

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_contDiff_mul_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U)
    {χ f : E → ℝ} {n : WithTop ℕ∞} (hχ : ContDiff ℝ n χ) (hs : tsupport χ ⊆ U) (hf : ContDiffOn ℝ n f U) :
    ContDiff ℝ n (fun x => χ x * f x) := by sorry
