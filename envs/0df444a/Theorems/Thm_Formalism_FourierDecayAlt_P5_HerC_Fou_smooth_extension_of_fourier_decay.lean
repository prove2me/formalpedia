-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_smooth_extension_of_fourier_decay
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_extension_of_fourier_decay
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:24.658729+00:00
-- url     : https://prove2.me/theorems/a9ea60c9-94d5-407d-bc44-20f034200396
-- title:
--   Fou: smooth extension of fourier decay
-- statement:
--   The Fou construction uses the smooth extension of fourier decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousExtensionOfFourierDecay.lean#L19-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousExtensionOfFourierDecay.lean#L19-L49

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothBoundedOfFourierDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousExtensionOfFourierDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex Module
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_extension_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hE : Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t))
    (hc : ∀ t, t ≠ 0 → ContinuousAt D t)
    (hdD : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3)))
    (hdE : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ t, t ≠ 0 → D' t = D t) ∧ (∫ t, D' t = ∫ t, D t) ∧
      (∃ C', ∀ j ≤ m, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ C' * (1 + ‖t‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D') ∧ ∫ t, iteratedFDeriv ℝ j D' t = 0 := by sorry
