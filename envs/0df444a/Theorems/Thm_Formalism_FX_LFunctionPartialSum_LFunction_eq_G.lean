-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_LFunction_eq_G
-- name    : Formalism.FX.LFunctionPartialSum.LFunction_eq_G
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:06.938552+00:00
-- url     : https://prove2.me/theorems/4e1fa806-104c-4b60-befe-15f37264fd66
-- title:
--   LFunction Partial Sum: LFunction eq G
-- statement:
--   The LFunction Partial Sum construction uses the LFunction eq G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L228-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L228-L244

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

theorem Formalism.FX.LFunctionPartialSum.LFunction_eq_G (hχ : χ ≠ 1) {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = G χ s := by sorry
