-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_identity
-- name    : Formalism.FX.LFunctionPartialSum.partial_identity
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:55.023014+00:00
-- url     : https://prove2.me/theorems/4e6075eb-b6a9-442f-8d31-94e13724137f
-- title:
--   LFunction Partial Sum: partial identity
-- statement:
--   The LFunction Partial Sum construction uses the partial identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L129-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L129-L139

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

theorem Formalism.FX.LFunctionPartialSum.partial_identity (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm χ s n + Ap χ M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) * (n : ℂ) ^ (-s) := by sorry
