-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_isCompact_box
-- name    : Formalism.IncomingBounds.FlowLoadBounds.isCompact_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:06.657836+00:00
-- url     : https://prove2.me/theorems/7a1dc39f-a1f9-4864-a4dd-540c00aeb1cc
-- title:
--   Flow Load Bounds: is Compact box
-- statement:
--   The Flow Load Bounds construction uses the is Compact box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L97-L99

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

theorem Formalism.IncomingBounds.FlowLoadBounds.isCompact_box (R : ℝ) : IsCompact (box d R) := by sorry
