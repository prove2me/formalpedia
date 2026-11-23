-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_dil_sym
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_dil_sym
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:02.49381+00:00
-- url     : https://prove2.me/theorems/b9e85945-171b-475b-bdfe-f67d12c6c3c9
-- title:
--   Stationary Phase Model: D dil sym
-- statement:
--   The Stationary Phase Model construction uses the D dil sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1147-L1170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1147-L1170

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
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_dil_sym {N : ℕ} {h : E → F} {ρ₀ M : ℝ} (hh : ContDiff ℝ N h)
    (hs : tsupport h ⊆ Metric.closedBall 0 ρ₀) (hρ₀ : 0 ≤ ρ₀) (hM : ∀ x, ∀ i ≤ N, ‖iteratedFDeriv ℝ i h x‖ ≤ M)
    {R σ : ℝ} (hR : 1 ≤ R) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Sym Set.univ (wt σ) 0 N (M * (ρ₀ + 1) ^ N) (fun x => h (R⁻¹ • x)) := by sorry
