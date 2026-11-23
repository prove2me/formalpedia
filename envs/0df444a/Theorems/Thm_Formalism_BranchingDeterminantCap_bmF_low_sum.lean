-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_sum
-- name    : Formalism.BranchingDeterminantCap.bmF_low_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:05.022015+00:00
-- url     : https://prove2.me/theorems/409f621a-0765-4f48-8f3a-0e1e1975bbd1
-- title:
--   Branching Determinant Cap: bm F low sum
-- statement:
--   The Branching Determinant Cap construction uses the bm F low sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1624-L1627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1624-L1627

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

theorem Formalism.BranchingDeterminantCap.bmF_low_sum {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {ι : Type*} (s : Finset ι) (L : ι → BP R n)
    (h : ∀ i ∈ s, IsLow D (L i)) : IsLow D (∑ i ∈ s, L i) := by sorry
