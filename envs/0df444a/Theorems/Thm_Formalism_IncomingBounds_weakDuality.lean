-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_weakDuality
-- name    : Formalism.IncomingBounds.weakDuality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:51.965903+00:00
-- url     : https://prove2.me/theorems/948f2721-7a2e-4bbc-ad12-5f3577b15d87
-- title:
--   Incoming Bounds: weak Duality
-- statement:
--   The Incoming Bounds construction uses the weak Duality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L420-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L420-L423

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
open FlowLoadBounds

theorem Formalism.IncomingBounds.weakDuality (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (sig : ZMod d → ℝ) (hx : IsFlow l d D x) (hsig : IsDual l d sig) :
    flowVal d x ≤ ∑ s, D s * sig s := by sorry
