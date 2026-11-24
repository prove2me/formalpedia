-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_clip_dual
-- name    : Formalism.IncomingBounds.FlowLoadBounds.clip_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:39.624849+00:00
-- url     : https://prove2.me/theorems/def5f58f-94d4-4a56-8224-f8b3aaa53b0a
-- title:
--   Flow Load Bounds: clip dual
-- statement:
--   The Flow Load Bounds construction uses the clip dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L338-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L338-L357

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

theorem Formalism.IncomingBounds.FlowLoadBounds.clip_dual (hl : 1 ≤ l) {τ : ZMod d → ℝ} (h0 : ∀ s, 0 ≤ τ s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * τ s + τ (s + (i : ZMod d))) :
    IsDual l d (fun s => min (τ s) 1) := by sorry
