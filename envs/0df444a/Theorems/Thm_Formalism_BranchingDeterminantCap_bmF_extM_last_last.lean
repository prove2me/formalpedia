-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_extM_last_last
-- name    : Formalism.BranchingDeterminantCap.bmF_extM_last_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:55.920465+00:00
-- url     : https://prove2.me/theorems/a3209cb2-e74b-47e9-89ef-ef3a780c438d
-- title:
--   Branching Determinant Cap: bm F ext M last last
-- statement:
--   The Branching Determinant Cap construction uses the bm F ext M last last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1888-L1890
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean#L1888-L1890

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

theorem Formalism.BranchingDeterminantCap.bmF_extM_last_last (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    extM R g (Fin.last n) (Fin.last n) = 1 := by sorry
