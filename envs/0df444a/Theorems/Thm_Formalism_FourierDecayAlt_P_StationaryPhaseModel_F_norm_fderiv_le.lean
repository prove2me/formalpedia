-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_norm_fderiv_le
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_norm_fderiv_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:05.167976+00:00
-- url     : https://prove2.me/theorems/f241aab0-339e-4344-bd05-35693d8ae802
-- title:
--   Stationary Phase Model: F norm fderiv le
-- statement:
--   The Stationary Phase Model construction uses the F norm fderiv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2694-L2705
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2694-L2705

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
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_norm_fderiv_le {f : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (Metric.ball x (2 * δ))) (hM : ∀ y ∈ Metric.ball x (2 * δ), ‖f y‖ ≤ M)
    (v : Fin d → ℂ) : ‖fderiv ℂ f x v‖ ≤ M / δ * ‖v‖ := by sorry
