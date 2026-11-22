-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_omg_single
-- name    : Formalism.BranchingDeterminantCap.bmD_omg_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:36.940814+00:00
-- url     : https://prove2.me/theorems/7213d418-5b4f-4ee7-8161-b3a28eba1846
-- title:
--   Branching Determinant Cap: bm D omg single
-- statement:
--   The Branching Determinant Cap construction uses the bm D omg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1385-L1387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1385-L1387

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

theorem Formalism.BranchingDeterminantCap.bmD_omg_single {n : ℕ} (s : Fin n) :
    omg (Pi.single s 1 : Fin n → ℤ) = ((s : ℕ) : ℤ) + 1 := by sorry
