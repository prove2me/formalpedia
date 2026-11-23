-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comp_ne_iff
-- name    : Formalism.BranchingDeterminantCap.bmE_comp_ne_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:40.698448+00:00
-- url     : https://prove2.me/theorems/9a74d180-43c6-4a62-b913-b9ecc23cefbb
-- title:
--   Branching Determinant Cap: bm E comp ne iff
-- statement:
--   The Branching Determinant Cap construction uses the bm E comp ne iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1084-L1100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1084-L1100

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

theorem Formalism.BranchingDeterminantCap.bmE_comp_ne_iff {R σ B : Type*} [CommRing R] [AddCommMonoid B] [DecidableEq B] (w : σ → B)
    (G : MvPolynomial σ R) (β : B) :
    weightedHomogeneousComponent w β G ≠ 0 ↔ β ∈ G.support.image (Finsupp.weight w) := by sorry
