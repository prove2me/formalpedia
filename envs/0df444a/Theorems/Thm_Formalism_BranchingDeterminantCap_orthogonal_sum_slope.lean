-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_orthogonal_sum_slope
-- name    : Formalism.BranchingDeterminantCap.orthogonal_sum_slope
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:39:54.850866+00:00
-- url     : https://prove2.me/theorems/1dd7899f-89b0-5a8d-81c0-0d1739ee931e
-- title:
--   Branching Determinant Cap: orthogonal sum slope
-- statement:
--   The Branching Determinant Cap construction uses the orthogonal sum slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L125-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/OrthSum.lean#L125-L142

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_F_orthogonal_sum_slope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open OrthogonalSumAlt

theorem Formalism.BranchingDeterminantCap.orthogonal_sum_slope : OrthSum := by sorry
