-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_weylDimBound
-- name    : Formalism.BranchingDeterminantCap.weylDimBound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:33.596619+00:00
-- url     : https://prove2.me/theorems/a6a01438-6ab0-4889-9dd6-c95937aa4f41
-- title:
--   Branching Determinant Cap: weyl Dim Bound
-- statement:
--   The Branching Determinant Cap construction uses the weyl Dim Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/DivFromPassageAndNorm.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/DivFromPassageAndNorm.lean#L31-L31

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
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.weylDimBound : WeylDimBound := by sorry
