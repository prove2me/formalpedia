-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_summable_dterm
-- name    : Formalism.FX.LFunctionPartialSum.summable_dterm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:05.128965+00:00
-- url     : https://prove2.me/theorems/a23aed2a-34c8-4902-a6e2-1880b99b56f3
-- title:
--   LFunction Partial Sum: summable dterm
-- statement:
--   The LFunction Partial Sum construction uses the summable dterm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L126-L127

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

theorem Formalism.FX.LFunctionPartialSum.summable_dterm {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (dterm χ s) := by sorry
