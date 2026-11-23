-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_strong
-- name    : Formalism.IncomingBounds.FlowLoadBounds.strong
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:17.886321+00:00
-- url     : https://prove2.me/theorems/bd67a091-eb5d-4b98-bd88-0e8397c4863c
-- title:
--   Flow Load Bounds: strong
-- statement:
--   The Flow Load Bounds construction uses the strong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L377-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L377-L397

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

theorem Formalism.IncomingBounds.FlowLoadBounds.strong (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ ∑ s, D s * sig s = maxFlow l d D := by sorry
