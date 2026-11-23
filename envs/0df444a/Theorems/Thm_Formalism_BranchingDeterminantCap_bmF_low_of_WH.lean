-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_of_WH
-- name    : Formalism.BranchingDeterminantCap.bmF_low_of_WH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:10.85378+00:00
-- url     : https://prove2.me/theorems/d07e6839-f544-44dd-9efc-a7ff50a47650
-- title:
--   Branching Determinant Cap: bm F low of WH
-- statement:
--   The Branching Determinant Cap construction uses the bm F low of WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1629-L1633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1629-L1633

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

theorem Formalism.BranchingDeterminantCap.bmF_low_of_WH {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {F : BP R n} {β : Fin n → ℤ}
    (hF : IsWeightedHomogeneous (zW n) F β) (hβ : omg β < D) : IsLow D F := by sorry
