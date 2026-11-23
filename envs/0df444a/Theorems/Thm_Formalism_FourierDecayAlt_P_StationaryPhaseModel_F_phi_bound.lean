-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:07.063128+00:00
-- url     : https://prove2.me/theorems/67e82642-1926-4269-a920-2715e8c21c79
-- title:
--   Stationary Phase Model: F phi bound
-- statement:
--   The Stationary Phase Model construction uses the F phi bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2839-L2850
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2839-L2850

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_bound (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r)))
    (hb : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) (i : ℕ) {δ : ℝ} (hδ : 0 < δ) (hi : ((i + 1 : ℕ) : ℝ) * δ ≤ r) :
    ‖iteratedFDeriv ℝ i (F_phi d r c g) x‖ ≤ ‖c‖ * (Λ / δ ^ i) := by sorry
