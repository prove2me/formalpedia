-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_ZW
-- name    : Formalism.BranchingDeterminantCap.bmK_ZW
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:48.876226+00:00
-- url     : https://prove2.me/theorems/3d66320d-740a-4e79-b6b3-9920715a1aca
-- title:
--   Branching Determinant Cap: bm K ZW
-- statement:
--   The Branching Determinant Cap construction uses the bm K ZW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2479-L2481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2479-L2481

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

theorem Formalism.BranchingDeterminantCap.bmK_ZW {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ) (d : ℕ)
    (G : BP R n) (hG : G ∈ bmW R n lam d) : bmZop R n lam sg G ∈ bmW R n lam d := by sorry
