-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmG_shift
-- name    : Formalism.BranchingDeterminantCap.bmG_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:05.918156+00:00
-- url     : https://prove2.me/theorems/0361bcdb-1822-454b-a6e7-51ae8e17dfd6
-- title:
--   Branching Determinant Cap: bm G shift
-- statement:
--   The Branching Determinant Cap construction uses the bm G shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2218-L2229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2218-L2229

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

theorem Formalism.BranchingDeterminantCap.bmG_shift {M : Type*} [CommMonoid M] (n : ℕ) (D : ℕ → M) (hD : D 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, D i.val ^ b i = ∏ i : Fin n, D (i.val + 1) ^ nuNext b i := by sorry
