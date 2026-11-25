-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_orthSum
-- name    : Formalism.BranchingDeterminantCap.orthSum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:53.426795+00:00
-- url     : https://prove2.me/theorems/099f8335-4d83-474a-b749-00952c1ea341
-- title:
--   Branching Determinant Cap: orth Sum
-- statement:
--   The Branching Determinant Cap construction uses the orth Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/DivFromPassageAndNorm.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/DivFromPassageAndNorm.lean#L21-L21

import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BoundsIVal
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementJ
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_StepDiii
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Theorems.Thm_Formalism_F_orthSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.orthSum : OrthSum := by sorry
