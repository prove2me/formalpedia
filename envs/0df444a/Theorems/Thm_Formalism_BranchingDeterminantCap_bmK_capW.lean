-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_capW
-- name    : Formalism.BranchingDeterminantCap.bmK_capW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:46.077293+00:00
-- url     : https://prove2.me/theorems/468732c6-ff74-45ae-be92-836160b68a97
-- title:
--   Branching Determinant Cap: bm K cap W
-- statement:
--   The Branching Determinant Cap construction uses the bm K cap W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2472-L2477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2472-L2477

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

theorem Formalism.BranchingDeterminantCap.bmK_capW {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (u : ℤ)
    (G : BP R n) (hG : G ∈ bmW R n lam d) : bmCap R n u G ∈ bmW R n lam d := by sorry
