-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_of_vanish
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.of_vanish
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:10.196277+00:00
-- url     : https://prove2.me/theorems/dc06498c-6253-44f1-817b-2fd0f58d5419
-- title:
--   Sym: of vanish
-- statement:
--   The Sym construction uses the of vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L305-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L305-L347

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.Sym.of_vanish {f : E → F} {r σ M : ℝ} (p : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hp : p ≤ N)
    (hf : ContDiff ℝ N f)
    (hM : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (h0 : ∀ i : ℕ, i < p → iteratedFDeriv ℝ i f 0 = 0) :
    Sym (Metric.closedBall (0 : E) r) (wt σ) p N (M * (r + 1) ^ N) f := by sorry
