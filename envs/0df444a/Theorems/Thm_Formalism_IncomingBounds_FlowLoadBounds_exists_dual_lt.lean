-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_exists_dual_lt
-- name    : Formalism.IncomingBounds.FlowLoadBounds.exists_dual_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:56.68064+00:00
-- url     : https://prove2.me/theorems/ab060adf-129e-4c4c-be69-9e797c547e7d
-- title:
--   Flow Load Bounds: exists dual lt
-- statement:
--   The Flow Load Bounds construction uses the exists dual lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L230-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L230-L336

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

theorem Formalism.IncomingBounds.FlowLoadBounds.exists_dual_lt (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) {v : ℝ}
    (hv : ∀ y, IsFlow l d D y → flowVal d y ≤ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ sig : ZMod d → ℝ, (∀ s, 0 ≤ sig s) ∧
      (∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) ∧
      ∑ s, D s * sig s < v + ε := by sorry
