-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_ite_derivation_apply
-- name    : Formalism.BranchingDeterminantCap.ite_derivation_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:34.46029+00:00
-- url     : https://prove2.me/theorems/c9ac4318-0735-4088-b86f-a2f49cb5ddca
-- title:
--   Branching Determinant Cap: ite derivation apply
-- statement:
--   The Branching Determinant Cap construction uses the ite derivation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L279-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L279-L281

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

theorem Formalism.BranchingDeterminantCap.ite_derivation_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (c : Prop) [Decidable c]
    (D : Derivation R A A) (x : A) : (if c then D else 0) x = if c then D x else 0 := by sorry
