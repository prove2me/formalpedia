-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le
-- name    : Formalism.FX.LFunctionPartialSum.norm_cpow_sub_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:01.086132+00:00
-- url     : https://prove2.me/theorems/5999561f-22c6-4dbc-8847-57a25568fb17
-- title:
--   LFunction Partial Sum: norm cpow sub le
-- statement:
--   The LFunction Partial Sum construction uses the norm cpow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L60-L67

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
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
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum

theorem Formalism.FX.LFunctionPartialSum.norm_cpow_sub_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by sorry
