-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:43.49415+00:00
-- url     : https://prove2.me/theorems/eb5cdb50-34ed-413c-88f9-9497fedae0bd
-- title:
--   Stationary Phase Model: D gau bound
-- statement:
--   The Stationary Phase Model construction uses the D gau bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1080-L1121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1080-L1121

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_bound (d N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
    (∀ x : Fin d → ℂ, ∀ i ≤ N, ‖iteratedFDeriv ℝ i (D_gau d δ) x‖ ≤ M) ∧
    Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 0 N M (D_gau d δ) := by sorry
