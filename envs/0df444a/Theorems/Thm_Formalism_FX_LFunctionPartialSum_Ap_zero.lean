-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_zero
-- name    : Formalism.FX.LFunctionPartialSum.Ap_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:06.341964+00:00
-- url     : https://prove2.me/theorems/6aff267a-4fcd-4d9a-83e9-5f5412bdf5ba
-- title:
--   LFunction Partial Sum: Ap zero
-- statement:
--   The LFunction Partial Sum construction uses the Ap zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L83-L84

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

theorem Formalism.FX.LFunctionPartialSum.Ap_zero : Ap χ 0 = 0 := by sorry
