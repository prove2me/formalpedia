-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmE
-- name    : Formalism.BranchingDeterminantCap.bmD_zcomp_bmE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:16.83945+00:00
-- url     : https://prove2.me/theorems/d7713984-b2d1-4e3c-b41b-27f24d18f8eb
-- title:
--   Branching Determinant Cap: bm D zcomp bm E
-- statement:
--   The Branching Determinant Cap construction uses the bm D zcomp bm E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1393-L1395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1393-L1395

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

theorem Formalism.BranchingDeterminantCap.bmD_zcomp_bmE {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (s t : Fin n) (Y : BP R n) :
    zcomp R n β (bmE R n s t Y) = bmE R n s t (zcomp R n β Y) := by sorry
