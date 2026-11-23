-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_load_trunc
-- name    : Formalism.IncomingBounds.FlowLoadBounds.load_trunc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:43.416817+00:00
-- url     : https://prove2.me/theorems/961fe3ef-dc1e-4f31-8b71-b30ce4f730e3
-- title:
--   Flow Load Bounds: load trunc
-- statement:
--   The Flow Load Bounds construction uses the load trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L71-L74

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

theorem Formalism.IncomingBounds.FlowLoadBounds.load_trunc (x : ZMod d → ℕ → ℝ) (s : ZMod d) :
    dpLoad l d (trunc d x) s = dpLoad l d x s := by sorry
