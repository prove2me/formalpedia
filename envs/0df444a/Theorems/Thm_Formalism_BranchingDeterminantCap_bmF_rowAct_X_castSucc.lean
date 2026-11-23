-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_X_castSucc
-- name    : Formalism.BranchingDeterminantCap.bmF_rowAct_X_castSucc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:21.721117+00:00
-- url     : https://prove2.me/theorems/ce9b8deb-d288-4ecb-8966-55c9aa864721
-- title:
--   Branching Determinant Cap: bm F row Act X cast Succ
-- statement:
--   The Branching Determinant Cap construction uses the bm F row Act X cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1892-L1895
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1892-L1895

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

theorem Formalism.BranchingDeterminantCap.bmF_rowAct_X_castSucc (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (a s : Fin n) :
    rowAct R (extM R g) (X (a.castSucc, s) : BP R n) = ∑ b : Fin n, C (g a b) * X (b.castSucc, s) := by sorry
