-- Prove2me | Theorems.Thm_Formalism_ZF_log_exp_add_two_bounds
-- name    : Formalism.ZF.log_exp_add_two_bounds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:42:15.478827+00:00
-- url     : https://prove2.me/theorems/f682a48c-17df-439c-aceb-f8f8fa332348
-- title:
--   ZF: log exp add two bounds
-- statement:
--   The ZF construction uses the log exp add two bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormIntegralComplLe.lean#L71-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormIntegralComplLe.lean#L71-L93

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

theorem Formalism.ZF.log_exp_add_two_bounds (c s : ℝ) (hc : 0 < c) (hs : 8 / c ≤ s) :
    1 ≤ Real.exp (c * s / 4) ∧ 1 ≤ Real.log (Real.exp (c * s / 4) + 2) ∧
      Real.log (Real.exp (c * s / 4) + 2) ≤ c * s / 2 := by sorry
