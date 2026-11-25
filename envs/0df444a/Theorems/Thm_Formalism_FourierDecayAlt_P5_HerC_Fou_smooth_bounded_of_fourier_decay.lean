-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_smooth_bounded_of_fourier_decay
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_bounded_of_fourier_decay
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:20.102807+00:00
-- url     : https://prove2.me/theorems/eae8934c-9b9d-562f-ac58-9164280e15a0
-- title:
--   Fou: smooth bounded of fourier decay
-- statement:
--   The Fou construction uses the smooth bounded of fourier decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothBoundedOfFourierDecay.lean#L34-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothBoundedOfFourierDecay.lean#L34-L62

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MomentIntegrable
import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothBoundedOfFourierDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex
open scoped FourierTransform ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_bounded_of_fourier_decay (D : ℂ → ℂ) (m : ℕ) (C : ℝ) (hD : Integrable D)
    (hdec : ∀ s, ‖∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((m : ℝ) + 3))) :
    ∃ D' : ℂ → ℂ, ContDiff ℝ m D' ∧ (∀ j ≤ m, ∃ B, ∀ t, ‖iteratedFDeriv ℝ j D' t‖ ≤ B) ∧
      ∀ t, ContinuousAt D t → D' t = D t := by sorry
