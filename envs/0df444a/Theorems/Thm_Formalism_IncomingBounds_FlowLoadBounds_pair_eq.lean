-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_pair_eq
-- name    : Formalism.IncomingBounds.FlowLoadBounds.pair_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:07.864802+00:00
-- url     : https://prove2.me/theorems/a2c80e8e-46b2-4d44-a289-9b8e79289abe
-- title:
--   Flow Load Bounds: pair eq
-- statement:
--   The Flow Load Bounds construction uses the pair eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L22-L32

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

theorem Formalism.IncomingBounds.FlowLoadBounds.pair_eq (x : ZMod d → ℕ → ℝ) (a : ZMod d → ℝ) :
    ∑ s, a s * dpLoad l d x s =
      ∑ s, ∑ i ∈ oddLevels d, ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * x s i := by sorry
