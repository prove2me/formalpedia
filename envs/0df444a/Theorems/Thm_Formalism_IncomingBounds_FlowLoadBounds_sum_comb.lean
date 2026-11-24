-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_sum_comb
-- name    : Formalism.IncomingBounds.FlowLoadBounds.sum_comb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:51.797779+00:00
-- url     : https://prove2.me/theorems/a081c21b-ee39-4205-a24a-8c15793afe95
-- title:
--   Flow Load Bounds: sum comb
-- statement:
--   The Flow Load Bounds construction uses the sum comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L144-L147

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

theorem Formalism.IncomingBounds.FlowLoadBounds.sum_comb {ι : Type*} (S : Finset ι) (f g c : ι → ℝ) (a b : ℝ) :
    ∑ i ∈ S, c i * (a * f i + b * g i) = a * ∑ i ∈ S, c i * f i + b * ∑ i ∈ S, c i * g i := by sorry
