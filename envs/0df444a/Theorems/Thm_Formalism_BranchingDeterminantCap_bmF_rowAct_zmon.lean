-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_zmon
-- name    : Formalism.BranchingDeterminantCap.bmF_rowAct_zmon
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:31.141219+00:00
-- url     : https://prove2.me/theorems/79450133-112c-43e5-a561-ccaf5599c522
-- title:
--   Branching Determinant Cap: bm F row Act zmon
-- statement:
--   The Branching Determinant Cap construction uses the bm F row Act zmon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1902-L1904
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1902-L1904

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

theorem Formalism.BranchingDeterminantCap.bmF_rowAct_zmon (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) :
    rowAct R (extM R g) (zmon R n b) = zmon R n b := by sorry
