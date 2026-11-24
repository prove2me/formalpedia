-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_fd_part1
-- name    : Formalism.IncomingBounds.FlowDualityReindexing.fd_part1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:01.586694+00:00
-- url     : https://prove2.me/theorems/c0a1cfdd-d572-460c-acba-06f2566d0426
-- title:
--   Flow Duality Reindexing: fd part1
-- statement:
--   The Flow Duality Reindexing construction uses the fd part1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L140-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L140-L169

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

theorem Formalism.IncomingBounds.FlowDualityReindexing.fd_part1 (hl : 3 ≤ l) (D sig : ZMod d → ℝ) (hopt : IsOptDual l d D sig) (s : ZMod d)
    (hs : 2 / (l : ℝ) ≤ sig s) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x)
    (hval : flowVal d x = maxFlow l d D) :
    (∀ i ∈ oddLevels d, x s i = 0) ∧ D s = ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by sorry
