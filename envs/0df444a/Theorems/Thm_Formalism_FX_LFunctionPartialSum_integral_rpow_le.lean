-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_integral_rpow_le
-- name    : Formalism.FX.LFunctionPartialSum.integral_rpow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:03.482163+00:00
-- url     : https://prove2.me/theorems/8ce0b0e9-2760-4aa0-a6c2-f5d2d065b497
-- title:
--   LFunction Partial Sum: integral rpow le
-- statement:
--   The LFunction Partial Sum construction uses the integral rpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L50-L58

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

theorem Formalism.FX.LFunctionPartialSum.integral_rpow_le {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in x..(x + 1), t ^ (-σ - 1) ≤ x ^ (-σ - 1) := by sorry
