-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_central
-- name    : Formalism.BranchingDeterminantCap.capDet_central
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:26.746455+00:00
-- url     : https://prove2.me/theorems/1b9cb7ef-1999-4337-addb-ee693b432689
-- title:
--   Branching Determinant Cap: cap Det central
-- statement:
--   The Branching Determinant Cap construction uses the cap Det central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L804-L857
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L804-L857

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem Formalism.BranchingDeterminantCap.capDet_central {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (k l : Fin n) : Commute (E k l) (capDet E u) := by sorry
