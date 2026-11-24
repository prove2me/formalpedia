-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_flow_le
-- name    : Formalism.IncomingBounds.FlowDualityReindexing.flow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:47.290807+00:00
-- url     : https://prove2.me/theorems/88ab9030-6f13-4b42-b3f2-9fd1a2661fc5
-- title:
--   Flow Duality Reindexing: flow le
-- statement:
--   The Flow Duality Reindexing construction uses the flow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L85-L94

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
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
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowDualityReindexing
variable {l d : ℕ} [NeZero d]

theorem Formalism.IncomingBounds.FlowDualityReindexing.flow_le (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x) (t : ZMod d)
    (i : ℕ) (hi : i ∈ oddLevels d) : (l : ℝ) ^ i * x t i ≤ D t := by sorry
