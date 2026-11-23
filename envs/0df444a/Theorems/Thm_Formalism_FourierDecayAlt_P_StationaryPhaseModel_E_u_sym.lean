-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_u_sym
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_u_sym
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:46.740181+00:00
-- url     : https://prove2.me/theorems/bde3f62b-df9b-4d1e-a621-a74482af0ff3
-- title:
--   Stationary Phase Model: E u sym
-- statement:
--   The Stationary Phase Model construction uses the E u sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2419-L2459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2419-L2459

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
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_u_sym (hr : 0 < r) (hρ0 : 0 < ρ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hCχ : 0 ≤ Cχ)
    (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ (2 * d + 2 : ℕ) a)
    (hbd : ∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r) (wt (Real.sqrt τ)) 2 (d + 2)
      ((S + 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2) * S) * (r + 1) ^ (d + 2)) (E_u d ρ a) := by sorry
