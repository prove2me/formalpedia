-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_list_mem
-- name    : Formalism.BranchingDeterminantCap.bmK_list_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:53.225803+00:00
-- url     : https://prove2.me/theorems/4d466366-f051-4e4c-bee7-ae3df5f0ce3b
-- title:
--   Branching Determinant Cap: bm K list mem
-- statement:
--   The Branching Determinant Cap construction uses the bm K list mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2435-L2442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L2435-L2442

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

theorem Formalism.BranchingDeterminantCap.bmK_list_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (C : ℤ → Module.End R M)
    (W : Submodule R M) (hC : ∀ u, ∀ G ∈ W, C u G ∈ W) (ℓ : List ℤ) : ∀ G ∈ W, (ℓ.map C).prod G ∈ W := by sorry
