-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_LFunction_eq_G_of_one_lt
-- name    : Formalism.FX.LFunctionPartialSum.LFunction_eq_G_of_one_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:17.808203+00:00
-- url     : https://prove2.me/theorems/78517eb6-4c93-44e8-8b07-0a2020f57e3f
-- title:
--   LFunction Partial Sum: LFunction eq G of one lt
-- statement:
--   The LFunction Partial Sum construction uses the LFunction eq G of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L213-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L213-L226

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

theorem Formalism.FX.LFunctionPartialSum.LFunction_eq_G_of_one_lt {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = G χ s := by sorry
