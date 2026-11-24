-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_isCompact_dual
-- name    : Formalism.IncomingBounds.FlowLoadBounds.isCompact_dual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:54.540957+00:00
-- url     : https://prove2.me/theorems/8b2bbe6c-eb07-4641-a54d-48cf40a89903
-- title:
--   Flow Load Bounds: is Compact dual
-- statement:
--   The Flow Load Bounds construction uses the is Compact dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L359-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L359-L375

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

theorem Formalism.IncomingBounds.FlowLoadBounds.isCompact_dual : IsCompact {sig : ZMod d → ℝ | IsDual l d sig} := by sorry
