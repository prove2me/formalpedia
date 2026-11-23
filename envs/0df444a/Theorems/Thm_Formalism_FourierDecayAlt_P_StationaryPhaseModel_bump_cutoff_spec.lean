-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_bump_cutoff_spec
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.bump_cutoff_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:59.070203+00:00
-- url     : https://prove2.me/theorems/bdf02691-9924-46d3-a40d-4e499791288d
-- title:
--   Stationary Phase Model: bump cutoff spec
-- statement:
--   The Stationary Phase Model construction uses the bump cutoff spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L3117-L3135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L3117-L3135

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
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.bump_cutoff_spec (d : ℕ) (ρ : ℝ) (h : 0 < ρ) (n : ℕ) :
    ContDiff ℝ n (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ∧
    HasCompactSupport (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ∧
    Function.support (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) ⊆ Metric.closedBall 0 ρ ∧
    ((cutB d ρ (0 : Fin d → ℂ) : ℝ) : ℂ) = 1 := by sorry
