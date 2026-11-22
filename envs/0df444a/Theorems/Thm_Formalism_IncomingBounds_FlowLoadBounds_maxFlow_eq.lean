-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_maxFlow_eq
-- name    : Formalism.IncomingBounds.FlowLoadBounds.maxFlow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:45.027941+00:00
-- url     : https://prove2.me/theorems/1fff949b-79e9-48c7-ab27-3cbb6468903d
-- title:
--   Flow Load Bounds: max Flow eq
-- statement:
--   The Flow Load Bounds construction uses the max Flow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L137-L142

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

theorem Formalism.IncomingBounds.FlowLoadBounds.maxFlow_eq {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x)
    (hmax : ∀ y, IsFlow l d D y → flowVal d y ≤ flowVal d x) : maxFlow l d D = flowVal d x := by sorry
