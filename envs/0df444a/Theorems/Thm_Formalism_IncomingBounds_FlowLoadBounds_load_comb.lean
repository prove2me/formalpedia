-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_load_comb
-- name    : Formalism.IncomingBounds.FlowLoadBounds.load_comb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:48.505512+00:00
-- url     : https://prove2.me/theorems/1ecf2181-bb3c-4e3a-ae56-2b4578a69378
-- title:
--   Flow Load Bounds: load comb
-- statement:
--   The Flow Load Bounds construction uses the load comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L153-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L153-L163

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

theorem Formalism.IncomingBounds.FlowLoadBounds.load_comb (x y : ZMod d → ℕ → ℝ) (a b : ℝ) (s : ZMod d) :
    dpLoad l d (fun s i => a * x s i + b * y s i) s = a * dpLoad l d x s + b * dpLoad l d y s := by sorry
