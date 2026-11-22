-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bm_list_eigen
-- name    : Formalism.BranchingDeterminantCap.bm_list_eigen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:51.671326+00:00
-- url     : https://prove2.me/theorems/11e3455b-c365-4cf8-b064-69e214c5844b
-- title:
--   Branching Determinant Cap: bm list eigen
-- statement:
--   The Branching Determinant Cap construction uses the bm list eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1059-L1070
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1059-L1070

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem Formalism.BranchingDeterminantCap.bm_list_eigen {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (C : ℤ → Module.End R M)
    (χ : ℤ → ℤ) (v : M) (h : ∀ u, C u v = ((χ u : ℤ) : R) • v) (ℓ : List ℤ) :
    (ℓ.map C).prod v = (((ℓ.map χ).prod : ℤ) : R) • v := by sorry
