-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_lie_bracket
-- name    : Formalism.BranchingDeterminantCap.elemDeriv_lie_bracket
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:38.020077+00:00
-- url     : https://prove2.me/theorems/a288402a-5e3b-4166-8957-0f82c5fedc4e
-- title:
--   Branching Determinant Cap: elem Deriv lie bracket
-- statement:
--   The Branching Determinant Cap construction uses the elem Deriv lie bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L287-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L287-L295

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap

theorem Formalism.BranchingDeterminantCap.elemDeriv_lie_bracket (R : Type*) [CommRing R] (n : ℕ) (i j k l : Fin n) :
    ⁅bmE R n i j, bmE R n k l⁆ =
      (if j = k then bmE R n i l else 0) - (if i = l then bmE R n k j else 0) := by sorry
