-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_partial_tendsto_G
-- name    : Formalism.FX.LFunctionPartialSum.partial_tendsto_G
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:41.072742+00:00
-- url     : https://prove2.me/theorems/0d820234-175a-4891-b7c9-cb97998c8971
-- title:
--   LFunction Partial Sum: partial tendsto G
-- statement:
--   The LFunction Partial Sum construction uses the partial tendsto G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L191-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LFunctionEqGOfOneLt.lean#L191-L211

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

theorem Formalism.FX.LFunctionPartialSum.partial_tendsto_G {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) * (n : ℂ) ^ (-s)) atTop
      (𝓝 (G χ s)) := by sorry
