-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_continuous_load
-- name    : Formalism.IncomingBounds.FlowLoadBounds.continuous_load
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:16.934323+00:00
-- url     : https://prove2.me/theorems/75dd1794-d1c8-484e-8a70-aa379a5d8098
-- title:
--   Flow Load Bounds: continuous load
-- statement:
--   The Flow Load Bounds construction uses the continuous load property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L60-L62

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

theorem Formalism.IncomingBounds.FlowLoadBounds.continuous_load (s : ZMod d) : Continuous fun x : ZMod d → ℕ → ℝ => dpLoad l d x s := by sorry
