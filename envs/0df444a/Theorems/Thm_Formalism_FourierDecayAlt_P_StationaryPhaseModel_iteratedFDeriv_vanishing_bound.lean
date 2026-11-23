-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_iteratedFDeriv_vanishing_bound
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.iteratedFDeriv_vanishing_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:17.934289+00:00
-- url     : https://prove2.me/theorems/a747d949-2d77-4c63-bddc-283076a2a123
-- title:
--   Stationary Phase Model: iterated FDeriv vanishing bound
-- statement:
--   The Stationary Phase Model construction uses the iterated FDeriv vanishing bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L274-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L274-L303

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.iteratedFDeriv_vanishing_bound {f : E → F} {r M : ℝ} (p : ℕ) (hp : p ≤ N) (hf : ContDiff ℝ N f)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (h0 : ∀ i : ℕ, i < p → iteratedFDeriv ℝ i f 0 = 0) (k : ℕ) (hk : k ≤ p) :
    ∀ x ∈ Metric.closedBall (0 : E) r, ‖iteratedFDeriv ℝ (p - k) f x‖ ≤ M * ‖x‖ ^ k := by sorry
