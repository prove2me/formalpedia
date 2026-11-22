-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_derivation_apply_ite
-- name    : Formalism.BranchingDeterminantCap.derivation_apply_ite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:45.788049+00:00
-- url     : https://prove2.me/theorems/f9f5fe1d-a3ff-48fb-8005-adbcc32000f9
-- title:
--   Branching Determinant Cap: derivation apply ite
-- statement:
--   The Branching Determinant Cap construction uses the derivation apply ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L283-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L283-L285

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

theorem Formalism.BranchingDeterminantCap.derivation_apply_ite {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (c : Prop) [Decidable c]
    (D : Derivation R A A) (x : A) : D (if c then x else 0) = if c then D x else 0 := by sorry
