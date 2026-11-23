-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_bump_cutoff_deriv_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.bump_cutoff_deriv_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:27.405806+00:00
-- url     : https://prove2.me/theorems/117c9a32-15f2-4d05-9ead-2470321def97
-- title:
--   Stationary Phase Model: bump cutoff deriv bound
-- statement:
--   The Stationary Phase Model construction uses the bump cutoff deriv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L3137-L3148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L3137-L3148

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.bump_cutoff_deriv_bound (d : ℕ) (ρ : ℝ) (h : 0 < ρ) (n : ℕ) : ∃ S : ℝ, ∀ j ≤ n, ∀ x : Fin d → ℂ,
    ‖iteratedFDeriv ℝ j (fun x : Fin d → ℂ => ((cutB d ρ x : ℝ) : ℂ)) x‖ ≤ S := by sorry
