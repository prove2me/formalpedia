-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_extM_castSucc_last
-- name    : Formalism.BranchingDeterminantCap.bmF_extM_castSucc_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:46.287089+00:00
-- url     : https://prove2.me/theorems/61ef58d6-dcbe-4086-8f7a-c4aea5d36eb8
-- title:
--   Branching Determinant Cap: bm F ext M cast Succ last
-- statement:
--   The Branching Determinant Cap construction uses the bm F ext M cast Succ last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1880-L1882
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1880-L1882

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

theorem Formalism.BranchingDeterminantCap.bmF_extM_castSucc_last (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (a : Fin n) :
    extM R g a.castSucc (Fin.last n) = 0 := by sorry
