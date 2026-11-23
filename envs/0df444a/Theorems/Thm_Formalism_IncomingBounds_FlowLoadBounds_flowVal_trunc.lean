-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_flowVal_trunc
-- name    : Formalism.IncomingBounds.FlowLoadBounds.flowVal_trunc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:20.410471+00:00
-- url     : https://prove2.me/theorems/c9aa476c-39b3-41a8-a8b8-62f66b9ab827
-- title:
--   Flow Load Bounds: flow Val trunc
-- statement:
--   The Flow Load Bounds construction uses the flow Val trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L76-L78

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

theorem Formalism.IncomingBounds.FlowLoadBounds.flowVal_trunc (x : ZMod d → ℕ → ℝ) : flowVal d (trunc d x) = flowVal d x := by sorry
