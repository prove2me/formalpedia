-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_integral_le
-- name    : Formalism.FX.LFunctionPartialSum.norm_integral_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:34.339869+00:00
-- url     : https://prove2.me/theorems/e1584388-8ae2-4e76-9b9c-92c4c53f814d
-- title:
--   LFunction Partial Sum: norm integral le
-- statement:
--   The LFunction Partial Sum construction uses the norm integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L34-L42

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

theorem Formalism.FX.LFunctionPartialSum.norm_integral_le {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1)‖ ≤ ∫ t in x..(x + 1), t ^ (-s.re - 1) := by sorry
