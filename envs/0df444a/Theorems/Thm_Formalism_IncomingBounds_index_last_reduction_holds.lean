-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_index_last_reduction_holds
-- name    : Formalism.IncomingBounds.index_last_reduction_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:11:35.528988+00:00
-- url     : https://prove2.me/theorems/f8d30f08-05c1-4076-8a66-df66bdcd88b0
-- title:
--   Incoming Bounds: index last reduction holds
-- statement:
--   The Incoming Bounds construction uses the index last reduction holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L86-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean#L86-L134

import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.LatticeIndexTer LatticeIndexAlt

theorem Formalism.IncomingBounds.index_last_reduction_holds : IndexLastStep := by sorry
