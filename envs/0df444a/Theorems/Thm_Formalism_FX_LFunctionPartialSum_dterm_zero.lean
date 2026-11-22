-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_dterm_zero
-- name    : Formalism.FX.LFunctionPartialSum.dterm_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:32.468891+00:00
-- url     : https://prove2.me/theorems/66192e1e-d713-4d32-b07d-7a778004dfdc
-- title:
--   LFunction Partial Sum: dterm zero
-- statement:
--   The LFunction Partial Sum construction uses the dterm zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L90-L91

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

theorem Formalism.FX.LFunctionPartialSum.dterm_zero (s : ℂ) : dterm χ s 0 = 0 := by sorry
