-- Prove2me | Theorems.Thm_Formalism_ZF_integral_eq_intervalIntegral_add_compl
-- name    : Formalism.ZF.integral_eq_intervalIntegral_add_compl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:03.530914+00:00
-- url     : https://prove2.me/theorems/59d559a1-f4a7-462a-8725-d4879b4a3750
-- title:
--   ZF: integral eq interval Integral add compl
-- statement:
--   The ZF construction uses the integral eq interval Integral add compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/IntegralEqIntervalIntegralAddCompl.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/IntegralEqIntervalIntegralAddCompl.lean#L36-L38

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.integral_eq_intervalIntegral_add_compl (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Set.Ioc (-T) T)ᶜ, f t := by sorry
