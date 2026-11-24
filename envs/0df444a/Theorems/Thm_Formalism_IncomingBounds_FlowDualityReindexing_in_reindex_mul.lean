-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_in_reindex_mul
-- name    : Formalism.IncomingBounds.FlowDualityReindexing.in_reindex_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:47.252828+00:00
-- url     : https://prove2.me/theorems/6f5bbe67-5bf4-4339-8051-747b8d0eb655
-- title:
--   Flow Duality Reindexing: in reindex mul
-- statement:
--   The Flow Duality Reindexing construction uses the in reindex mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L21-L29

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

theorem Formalism.IncomingBounds.FlowDualityReindexing.in_reindex_mul (sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, sig s * ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i =
      ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i * sig (s + (i : ZMod d)) := by sorry
