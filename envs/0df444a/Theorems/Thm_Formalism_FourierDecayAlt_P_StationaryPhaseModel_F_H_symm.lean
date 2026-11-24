-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_H_symm
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_H_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:59.72309+00:00
-- url     : https://prove2.me/theorems/c3fdf418-6935-4251-98fd-2f49aac2e0f8
-- title:
--   Stationary Phase Model: F H symm
-- statement:
--   The Stationary Phase Model construction uses the F H symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2681-L2686
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2681-L2686

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
variable {d : ℕ} {r : ℝ} {g : (Fin d → ℂ) → ℂ}
variable {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_H_symm (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hdg : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
      HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k))
    (hH : ∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) : H.IsSymm := by sorry
