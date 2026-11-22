-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_Ap_succ
-- name    : Formalism.FX.LFunctionPartialSum.Ap_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:43:30.397802+00:00
-- url     : https://prove2.me/theorems/9b5da855-faa3-4eab-a371-275941b15917
-- title:
--   LFunction Partial Sum: Ap succ
-- statement:
--   The LFunction Partial Sum construction uses the Ap succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L86-L88

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

theorem Formalism.FX.LFunctionPartialSum.Ap_succ (n : ℕ) : Ap χ (n + 1) = Ap χ n + χ ((n + 1 : ℕ) : ZMod q) := by sorry
