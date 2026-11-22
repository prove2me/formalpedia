-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmZ
-- name    : Formalism.BranchingDeterminantCap.bmD_zcomp_bmZ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:12.550353+00:00
-- url     : https://prove2.me/theorems/f488bcd0-b991-489b-bade-4481fe2f3084
-- title:
--   Branching Determinant Cap: bm D zcomp bm Z
-- statement:
--   The Branching Determinant Cap construction uses the bm D zcomp bm Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1397-L1401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1397-L1401

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

theorem Formalism.BranchingDeterminantCap.bmD_zcomp_bmZ {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (l j : Fin n) (Y : BP R n) :
    zcomp R n β (bmZ R n l j Y) =
      bmZ R n l j (zcomp R n (β - (Pi.single l 1 - Pi.single j 1)) Y) := by sorry
