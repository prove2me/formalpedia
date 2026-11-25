-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_branch_isometry
-- name    : Formalism.BranchingDeterminantCap.branch_isometry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:34.830204+00:00
-- url     : https://prove2.me/theorems/9a3e9442-0364-4b14-8488-f70c8c935ff3
-- title:
--   Branching Determinant Cap: branch isometry
-- statement:
--   The Branching Determinant Cap construction uses the branch isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L297-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean#L297-L334

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.branch_isometry : BranchIsometry := by sorry
