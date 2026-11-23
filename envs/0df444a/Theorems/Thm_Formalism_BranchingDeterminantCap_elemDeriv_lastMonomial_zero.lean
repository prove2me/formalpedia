-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_lastMonomial_zero
-- name    : Formalism.BranchingDeterminantCap.elemDeriv_lastMonomial_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:43.614533+00:00
-- url     : https://prove2.me/theorems/bcdfadc4-bbaa-4594-ab6e-c3250eaa78e7
-- title:
--   Branching Determinant Cap: elem Deriv last Monomial zero
-- statement:
--   The Branching Determinant Cap construction uses the elem Deriv last Monomial zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L478-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L478-L486

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

theorem Formalism.BranchingDeterminantCap.elemDeriv_lastMonomial_zero (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (b : Fin n → ℕ) :
    bmE R n s t (zmon R n b) = 0 := by sorry
