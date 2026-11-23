-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_rowAct_comm_bmEL
-- name    : Formalism.BranchingDeterminantCap.bm_rowAct_comm_bmEL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:47.587248+00:00
-- url     : https://prove2.me/theorems/ddc1b12e-afd8-4499-820c-065d1eedda88
-- title:
--   Branching Determinant Cap: bm row Act comm bm EL
-- statement:
--   The Branching Determinant Cap construction uses the bm row Act comm bm EL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L389-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L389-L396

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

theorem Formalism.BranchingDeterminantCap.bm_rowAct_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) (s t : Fin n) :
    Commute ((rowAct R (extM R g)).toLinearMap : Module.End R (BP R n)) (bmEL R n s t) := by sorry
