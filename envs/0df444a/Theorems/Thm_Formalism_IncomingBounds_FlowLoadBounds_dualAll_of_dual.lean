-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_dualAll_of_dual
-- name    : Formalism.IncomingBounds.FlowLoadBounds.dualAll_of_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:01.945619+00:00
-- url     : https://prove2.me/theorems/4027d785-93a1-4eac-955a-b881d5065f07
-- title:
--   Flow Load Bounds: dual All of dual
-- statement:
--   The Flow Load Bounds construction uses the dual All of dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L399-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean#L399-L414

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

theorem Formalism.IncomingBounds.FlowLoadBounds.dualAll_of_dual (hl : 1 ≤ l) (hev : Even d) {σ : ZMod d → ℝ} (h : IsDual l d σ) :
    IsDualAll l d σ := by sorry
