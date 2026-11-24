-- Prove2me | Theorems.Thm_Formalism_ZF_exp_mul_rpow_le
-- name    : Formalism.ZF.exp_mul_rpow_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:58.443131+00:00
-- url     : https://prove2.me/theorems/d7afaf64-b031-46b7-8041-5ceaf592ef94
-- title:
--   ZF: exp mul rpow le
-- statement:
--   The ZF construction uses the exp mul rpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormIntegralComplLe.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormIntegralComplLe.lean#L95-L107

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

theorem Formalism.ZF.exp_mul_rpow_le (y c L s : ℝ) (hy : 0 < y) (hℓ : Real.log y = s ^ 2) (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) (hL : 0 < L) (hLs : L ≤ c * s / 2) (hs : 0 < s) :
    Real.exp (c * s / 4) * y ^ (1 - c / L) ≤ y * Real.exp (-(c * s / 4)) := by sorry
