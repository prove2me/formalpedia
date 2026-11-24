-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_sum_inv_pow_le
-- name    : Formalism.IncomingBounds.FlowDualityReindexing.sum_inv_pow_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:36.976708+00:00
-- url     : https://prove2.me/theorems/0c59f9f8-5c3f-48db-92f4-5513874a2bc0
-- title:
--   Flow Duality Reindexing: sum inv pow le
-- statement:
--   The Flow Duality Reindexing construction uses the sum inv pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L103-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L103-L129

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

theorem Formalism.IncomingBounds.FlowDualityReindexing.sum_inv_pow_le (hl : 3 ≤ l) : ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹ ≤ gam l := by sorry
