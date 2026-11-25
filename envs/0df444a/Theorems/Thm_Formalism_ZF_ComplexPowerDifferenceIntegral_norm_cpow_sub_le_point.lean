-- Prove2me | Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_norm_cpow_sub_le_point
-- name    : Formalism.ZF.ComplexPowerDifferenceIntegral.norm_cpow_sub_le_point
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:42.267282+00:00
-- url     : https://prove2.me/theorems/662509ca-8b54-4197-a472-d1380cd98648
-- title:
--   Complex Power Difference Integral: norm cpow sub le point
-- statement:
--   The Complex Power Difference Integral construction uses the norm cpow sub le point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean#L22-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormCpowSubLePoint.lean#L22-L43

import Mathlib
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral

theorem Formalism.ZF.ComplexPowerDifferenceIntegral.norm_cpow_sub_le_point {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxa : x ≤ a + 1) {s : ℂ}
    (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by sorry
