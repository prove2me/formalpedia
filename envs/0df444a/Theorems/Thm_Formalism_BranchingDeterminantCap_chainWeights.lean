-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_chainWeights
-- name    : Formalism.BranchingDeterminantCap.chainWeights
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:22:15.457748+00:00
-- url     : https://prove2.me/theorems/5677fd9d-d987-491c-9f18-a979963bade8
-- title:
--   Branching Determinant Cap: chain Weights
-- statement:
--   The Branching Determinant Cap construction uses the chain Weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/ChainDenominatorCoupled.lean#L7-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/ChainDenominatorCoupled.lean#L7-L7

import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_BranchSandwichDivisors_ChainDenominatorCoupled
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.chainWeights : ChainWeights := by sorry
