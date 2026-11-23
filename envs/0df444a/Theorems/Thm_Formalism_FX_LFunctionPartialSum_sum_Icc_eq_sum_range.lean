-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_sum_Icc_eq_sum_range
-- name    : Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:49.169748+00:00
-- url     : https://prove2.me/theorems/6f7745cc-9eff-4cfb-85a3-ba2ac6519f1e
-- title:
--   LFunction Partial Sum: sum Icc eq sum range
-- statement:
--   The LFunction Partial Sum construction uses the sum Icc eq sum range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L183-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L183-L189

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

theorem Formalism.FX.LFunctionPartialSum.sum_Icc_eq_sum_range (f : ℕ → ℂ) (hf : f 0 = 0) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, f n = ∑ n ∈ Finset.range (M + 1), f n := by sorry
