-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_hasDerivAt_oscillatory_integral
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.hasDerivAt_oscillatory_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:17.400616+00:00
-- url     : https://prove2.me/theorems/c42326e8-1213-4a51-9b1a-45ca8a361713
-- title:
--   Stationary Phase Model: has Deriv At oscillatory integral
-- statement:
--   The Stationary Phase Model construction uses the has Deriv At oscillatory integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1634-L1661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1634-L1661

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.hasDerivAt_oscillatory_integral (hβ : β ≠ 0) (φ₀ P : (Fin d → ℂ) → ℝ) (hφ₀ : Continuous φ₀) (hP : Continuous P) (τ : ℝ)
    (c : (Fin d → ℂ) → V) (hc : Continuous c) (hcs : HasCompactSupport c) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, osc (fun y => φ₀ y + s * P y) τ x • c x ∂(muPi β (Fin d)))
      (∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c x) ∂(muPi β (Fin d))) s := by sorry
