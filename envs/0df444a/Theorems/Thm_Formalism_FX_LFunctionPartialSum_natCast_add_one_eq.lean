-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_natCast_add_one_eq
-- name    : Formalism.FX.LFunctionPartialSum.natCast_add_one_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:40:02.561813+00:00
-- url     : https://prove2.me/theorems/9065f85f-efc3-4a71-a8b5-5df261f58c5f
-- title:
--   LFunction Partial Sum: nat Cast add one eq
-- statement:
--   The LFunction Partial Sum construction uses the nat Cast add one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L93-L95

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

theorem Formalism.FX.LFunctionPartialSum.natCast_add_one_eq (n : ℕ) : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by sorry
