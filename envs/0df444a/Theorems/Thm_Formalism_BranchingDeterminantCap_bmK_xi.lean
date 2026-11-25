-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_xi
-- name    : Formalism.BranchingDeterminantCap.bmK_xi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:15.551301+00:00
-- url     : https://prove2.me/theorems/eedcab57-ceab-4fe3-a9a2-2ba741fa3283
-- title:
--   Branching Determinant Cap: bm K xi
-- statement:
--   The Branching Determinant Cap construction uses the bm K xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2537-L2573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2537-L2573

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

theorem Formalism.BranchingDeterminantCap.bmK_xi {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    bmZop R n lam sg (xiB R lam sg) = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg := by sorry
