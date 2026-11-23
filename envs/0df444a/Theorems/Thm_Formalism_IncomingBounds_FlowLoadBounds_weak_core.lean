-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_weak_core
-- name    : Formalism.IncomingBounds.FlowLoadBounds.weak_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:50.739801+00:00
-- url     : https://prove2.me/theorems/4a13525c-c7c6-4b35-8d0e-ea4191f8f548
-- title:
--   Flow Load Bounds: weak core
-- statement:
--   The Flow Load Bounds construction uses the weak core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L34-L45

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

theorem Formalism.IncomingBounds.FlowLoadBounds.weak_core {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} {sig : ZMod d → ℝ}
    (hx : IsFlow l d D x) (h0 : ∀ s, 0 ≤ sig s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) :
    flowVal d x ≤ ∑ s, D s * sig s := by sorry
