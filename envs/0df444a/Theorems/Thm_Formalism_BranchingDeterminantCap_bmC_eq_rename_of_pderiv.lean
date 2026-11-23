-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmC_eq_rename_of_pderiv
-- name    : Formalism.BranchingDeterminantCap.bmC_eq_rename_of_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:53.01432+00:00
-- url     : https://prove2.me/theorems/4d718d00-e57b-4af3-a60d-0d3540c73811
-- title:
--   Branching Determinant Cap: bm C eq rename of pderiv
-- statement:
--   The Branching Determinant Cap construction uses the bm C eq rename of pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L942-L964
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L942-L964

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

theorem Formalism.BranchingDeterminantCap.bmC_eq_rename_of_pderiv {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ}
    (H : MvPolynomial (Option (Fin r × Fin n)) R) (h : pderiv none H = 0) :
    H = rename some (ndEv R r n H) := by sorry
