-- Prove2me | Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_tail_le
-- name    : Formalism.FX.LFunctionPartialSum.norm_tail_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:32.831969+00:00
-- url     : https://prove2.me/theorems/6156895e-524c-4496-909e-8ff917607d93
-- title:
--   LFunction Partial Sum: norm tail le
-- statement:
--   The LFunction Partial Sum construction uses the norm tail le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean#L12-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/LPartialSum.lean#L12-L133

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
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
open LFunctionPartialSum

theorem Formalism.FX.LFunctionPartialSum.norm_tail_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {B : ℝ}
    (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by sorry
