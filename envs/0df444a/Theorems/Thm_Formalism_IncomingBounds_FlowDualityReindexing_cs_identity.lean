-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_cs_identity
-- name    : Formalism.IncomingBounds.FlowDualityReindexing.cs_identity
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:46.619795+00:00
-- url     : https://prove2.me/theorems/8e0bea19-74c0-422f-8dac-0eb5c3817860
-- title:
--   Flow Duality Reindexing: cs identity
-- statement:
--   The Flow Duality Reindexing construction uses the cs identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L31-L48

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

theorem Formalism.IncomingBounds.FlowDualityReindexing.cs_identity (D sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) :
    ∑ s : ZMod d, D s * sig s - flowVal d x =
      ∑ s : ZMod d, sig s * (D s - ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
        (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i))) +
      ∑ s : ZMod d, ∑ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) := by sorry
