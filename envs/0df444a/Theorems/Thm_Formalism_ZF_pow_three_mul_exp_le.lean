-- Prove2me | Theorems.Thm_Formalism_ZF_pow_three_mul_exp_le
-- name    : Formalism.ZF.pow_three_mul_exp_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:04.910547+00:00
-- url     : https://prove2.me/theorems/a19e67e7-a4e3-4409-933d-00af5af06a46
-- title:
--   ZF: pow three mul exp le
-- statement:
--   The ZF construction uses the pow three mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormIntegralComplLe.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormIntegralComplLe.lean#L45-L69

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
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

theorem Formalism.ZF.pow_three_mul_exp_le (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-(c * s / 4)) ≤ 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by sorry
