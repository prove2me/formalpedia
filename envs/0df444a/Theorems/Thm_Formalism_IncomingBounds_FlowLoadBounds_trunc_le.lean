-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_trunc_le
-- name    : Formalism.IncomingBounds.FlowLoadBounds.trunc_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:26.38478+00:00
-- url     : https://prove2.me/theorems/08e80d1c-2f5a-45f3-acbb-6770b63bd797
-- title:
--   Flow Load Bounds: trunc le
-- statement:
--   The Flow Load Bounds construction uses the trunc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L87-L93

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]

theorem Formalism.IncomingBounds.FlowLoadBounds.trunc_le (hl : 1 ≤ l) {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ s, dpLoad l d x s ≤ R) : ∀ s i, trunc d x s i ≤ R := by sorry
