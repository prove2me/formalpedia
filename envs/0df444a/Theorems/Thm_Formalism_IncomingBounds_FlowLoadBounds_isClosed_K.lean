-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_isClosed_K
-- name    : Formalism.IncomingBounds.FlowLoadBounds.isClosed_K
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:47.404734+00:00
-- url     : https://prove2.me/theorems/a9d7711f-bd88-4310-bcdf-08fa084ba124
-- title:
--   Flow Load Bounds: is Closed K
-- statement:
--   The Flow Load Bounds construction uses the is Closed K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L198-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L198-L228

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

theorem Formalism.IncomingBounds.FlowLoadBounds.isClosed_K (hl : 1 ≤ l) : IsClosed (Kset l d) := by sorry
