-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_cpow_sub_eq_integral
-- name    : Formalism.FX.LFunctionPartialSum.cpow_sub_eq_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:25.453262+00:00
-- url     : https://prove2.me/theorems/c068cb8c-9a5d-4b7a-84a4-e98f01b64d27
-- title:
--   LFunction Partial Sum: cpow sub eq integral
-- statement:
--   The LFunction Partial Sum construction uses the cpow sub eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L15-L32

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

theorem Formalism.FX.LFunctionPartialSum.cpow_sub_eq_integral {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s) = s * ∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1) := by sorry
