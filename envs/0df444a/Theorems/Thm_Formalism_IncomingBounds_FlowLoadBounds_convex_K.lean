-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_convex_K
-- name    : Formalism.IncomingBounds.FlowLoadBounds.convex_K
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:48.67253+00:00
-- url     : https://prove2.me/theorems/d81c1448-269f-4bd4-ae74-efeb9d7e66b7
-- title:
--   Flow Load Bounds: convex K
-- statement:
--   The Flow Load Bounds construction uses the convex K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L180-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L180-L191

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

theorem Formalism.IncomingBounds.FlowLoadBounds.convex_K : Convex ℝ (Kset l d) := by sorry
