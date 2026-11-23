-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_integral_rpow_eq
-- name    : Formalism.FX.LFunctionPartialSum.integral_rpow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:10.338725+00:00
-- url     : https://prove2.me/theorems/87c61cb7-6138-4ee1-b9dd-269ac7a93f62
-- title:
--   LFunction Partial Sum: integral rpow eq
-- statement:
--   The LFunction Partial Sum construction uses the integral rpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L44-L48

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

theorem Formalism.FX.LFunctionPartialSum.integral_rpow_eq {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in x..(x + 1), t ^ (-σ - 1) = (x ^ (-σ) - (x + 1) ^ (-σ)) / σ := by sorry
