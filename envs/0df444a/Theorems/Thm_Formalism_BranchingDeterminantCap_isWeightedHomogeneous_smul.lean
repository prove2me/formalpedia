-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_isWeightedHomogeneous_smul
-- name    : Formalism.BranchingDeterminantCap.isWeightedHomogeneous_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:43:26.364832+00:00
-- url     : https://prove2.me/theorems/46a7ffe1-01be-419e-bf44-8fcf03c8f618
-- title:
--   Branching Determinant Cap: is Weighted Homogeneous smul
-- statement:
--   The Branching Determinant Cap construction uses the is Weighted Homogeneous smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L87-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L87-L94

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

theorem Formalism.BranchingDeterminantCap.isWeightedHomogeneous_smul {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {β : B}
    {F : MvPolynomial σ R} (hF : IsWeightedHomogeneous w F β) (c : R) :
    IsWeightedHomogeneous w (c • F) β := by sorry
