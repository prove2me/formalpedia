-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_integral_fsv_eq_fourier
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.integral_fsv_eq_fourier
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:06.268501+00:00
-- url     : https://prove2.me/theorems/cff149f0-c928-4a2e-a4ea-737a051138f3
-- title:
--   Fou: integral fsv eq fourier
-- statement:
--   The Fou construction uses the integral fsv eq fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothBoundedOfFourierDecay.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothBoundedOfFourierDecay.lean#L11-L32

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

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.integral_fsv_eq_fourier (D : ℂ → ℂ) (s : ℂ) :
    ∫ t, Formalism.FourierDecayAlt.P5.fsv s t * D t = 𝓕 D (-(I * conj s) / (π : ℂ)) := by sorry
