-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_optdual_maxFlow
-- name    : Formalism.IncomingBounds.FlowDualityReindexing.optdual_maxFlow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:34.869845+00:00
-- url     : https://prove2.me/theorems/7e12d245-8b0e-4275-a783-35f04bffb12d
-- title:
--   Flow Duality Reindexing: optdual max Flow
-- statement:
--   The Flow Duality Reindexing construction uses the optdual max Flow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L50-L58

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

theorem Formalism.IncomingBounds.FlowDualityReindexing.optdual_maxFlow (D sig : ZMod d → ℝ) (h : IsOptDual l d D sig) :
    maxFlow l d D = ∑ s : ZMod d, D s * sig s := by sorry
