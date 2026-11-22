-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_dterm_le
-- name    : Formalism.FX.LFunctionPartialSum.norm_dterm_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:12.584588+00:00
-- url     : https://prove2.me/theorems/98215d55-965e-4412-8845-1fd3bc129382
-- title:
--   LFunction Partial Sum: norm dterm le
-- statement:
--   The LFunction Partial Sum construction uses the norm dterm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L97-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L97-L108

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
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.FX.LFunctionPartialSum.norm_dterm_le {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm χ s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by sorry
