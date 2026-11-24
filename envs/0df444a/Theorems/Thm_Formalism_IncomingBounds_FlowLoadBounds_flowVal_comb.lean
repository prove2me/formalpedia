-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_flowVal_comb
-- name    : Formalism.IncomingBounds.FlowLoadBounds.flowVal_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:52.284726+00:00
-- url     : https://prove2.me/theorems/a70a0785-c3ba-4c81-91cd-30f6f56bc90c
-- title:
--   Flow Load Bounds: flow Val comb
-- statement:
--   The Flow Load Bounds construction uses the flow Val comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L165-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L165-L170

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

theorem Formalism.IncomingBounds.FlowLoadBounds.flowVal_comb (x y : ZMod d → ℕ → ℝ) (a b : ℝ) :
    flowVal d (fun s i => a * x s i + b * y s i) = a * flowVal d x + b * flowVal d y := by sorry
