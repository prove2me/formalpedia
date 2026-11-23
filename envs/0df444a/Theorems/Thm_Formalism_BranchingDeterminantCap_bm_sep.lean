-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_sep
-- name    : Formalism.BranchingDeterminantCap.bm_sep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:30.206608+00:00
-- url     : https://prove2.me/theorems/f2d1eaa1-2de0-48e4-a658-ad9792d30620
-- title:
--   Branching Determinant Cap: bm sep
-- statement:
--   The Branching Determinant Cap construction uses the bm sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1301-L1323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1301-L1323

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

theorem Formalism.BranchingDeterminantCap.bm_sep {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (β β' : Fin n → ℤ) (h : bmAdm lam d β) (h' : bmAdm lam d β')
    (hne : β ≠ β') : ∃ u, bmChi lam β u ≠ bmChi lam β' u := by sorry
