-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_taylor
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_taylor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:37.92631+00:00
-- url     : https://prove2.me/theorems/158b8d2f-6f0b-4496-8726-0ec367d2b596
-- title:
--   Stationary Phase Model: E taylor
-- statement:
--   The Stationary Phase Model construction uses the E taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1663-L1727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1663-L1727

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
variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_taylor {d : ℕ} {β : ℂ} (hβ : β ≠ 0) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (φ₀ P : (Fin d → ℂ) → ℝ) (hφ₀ : Continuous φ₀) (hP : Continuous P) (τ : ℝ) (hτ : 0 < τ)
    (c : (Fin d → ℂ) → V) (hc : Continuous c) (hcs : HasCompactSupport c) (M : ℝ)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((P x * P x) • c x) ∂(muPi β (Fin d))‖ ≤ M) :
    ‖∫ x, osc (fun y => φ₀ y + P y) τ x • c x ∂(muPi β (Fin d)) - ∫ x, osc φ₀ τ x • c x ∂(muPi β (Fin d))
      - (Complex.I / (τ : ℂ)) • ∫ x, osc φ₀ τ x • (P x • c x) ∂(muPi β (Fin d))‖ ≤ M / τ ^ 2 := by sorry
