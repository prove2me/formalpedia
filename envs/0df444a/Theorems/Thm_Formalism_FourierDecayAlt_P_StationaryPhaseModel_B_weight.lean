-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_weight
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_weight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:48.499492+00:00
-- url     : https://prove2.me/theorems/44c55f27-0e84-4099-ad07-b297c40c68b1
-- title:
--   Stationary Phase Model: B weight
-- statement:
--   The Stationary Phase Model construction uses the B weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L399-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L399-L434

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_weight (d : ℕ) (β : ℂ) (hβ : β ≠ 0) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 0 < σ →
    Integrable (fun x : Fin d → ℂ => wt σ x ^ (-(2 * (d : ℤ) + 2))) (muPi β (Fin d)) ∧
    ∫ x : Fin d → ℂ, wt σ x ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)) ≤ C₀ / σ ^ 2 := by sorry
