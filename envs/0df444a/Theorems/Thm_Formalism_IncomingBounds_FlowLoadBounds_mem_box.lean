-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_mem_box
-- name    : Formalism.IncomingBounds.FlowLoadBounds.mem_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:47.962153+00:00
-- url     : https://prove2.me/theorems/2db074a9-980c-41d3-9ba6-094745eab87b
-- title:
--   Flow Load Bounds: mem box
-- statement:
--   The Flow Load Bounds construction uses the mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L101-L102

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

theorem Formalism.IncomingBounds.FlowLoadBounds.mem_box {R : ℝ} {x : ZMod d → ℕ → ℝ} : x ∈ box d R ↔ ∀ s i, 0 ≤ x s i ∧ x s i ≤ R := by sorry
